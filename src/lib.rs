//! This library implements a heapless linked list by keeping each element on the stack.
//!
//! The primary purpose is to efficiently keep a context when traversing trees recursively.
//!
//! Compared to a traditional linked list, this has a few drawbacks:
//! * Not "self-contained": you cannot easily store a `Node` as a member like you would a
//!   `LinkedList`.
//! * Many methods use recursion and lead to increase stack memory usage (because of function
//!   frames).
//!
//! The main advantage is that it does not need any heap allocation, and can grow to arbitrary
//! sizes (only limited by your stack size).
#![no_std]

/// A stack-based linked list.
///
/// This is a node in a traditional linked list. The main difference is that it does not box the
/// next element, but simply points to it. As a result, it is harder to pass around or to mutate,
/// but has the advantage of not requiring any heap allocation.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Node<'a, T> {
    /// An empty list.
    Root,
    /// A node in the list with some data and a tail.
    Head {
        /// Some data attached on this node. This is the first element of this list.
        data: T,
        /// The rest of the list as a tail node.
        tail: &'a Node<'a, T>,
    },
}

/// Convenient macro to define a stack list from a slice literal.
///
/// Note that this will actually define a bunch of local stack variables (one per item in the
/// list). This is _not_ an expression to define a standalone stack list, this would be impossible.
///
/// # Examples
///
/// ```rust
/// stack_list::stacklist!(let my_list = [1, 2, 3, 4]);
/// assert_eq!(my_list.len(), 4);
/// assert_eq!(my_list.get(3), Some(&4));
///
/// println!("{:?}", my_list);
/// ```
#[macro_export]
macro_rules! stacklist {
    ( let $name:ident = [ $head:expr $(,)? ] ) => {
        let root = $crate::Node::Root;
        let $name = root.prepend($head);
    };
    ( let $name:ident = [ $head:expr , $($tail:expr),* ] ) => {
        $crate::stacklist!(let n = [ $($tail),* ] );
        let $name = n.prepend($head);
    };
}

impl<'a, T> Node<'a, T> {
    /// Create a new empty list.
    pub fn new() -> Self {
        Node::Root
    }

    /// Create a new list by prepending `self` with `data`.
    pub fn prepend(&'a self, data: T) -> Self {
        Node::Head { data, tail: self }
    }

    /// Returns an iterator on this list.
    pub fn iter(&'a self) -> impl Iterator<Item = &'a T> {
        self
    }

    /// Run the given closure on each item from this list, starting from the end.
    pub fn for_each_rev<F>(&self, mut f: F)
    where
        F: FnMut(&T),
    {
        self.for_each_rev_inner(&mut f);
    }

    /// Same as `for_each_rev`, but takes a `&mut F` so it can more easily recurse.
    fn for_each_rev_inner<F>(&self, f: &mut F)
    where
        F: FnMut(&T),
    {
        if let &Node::Head { ref data, ref tail } = self {
            tail.for_each_rev_inner(f);
            f(data);
        }
    }

    /// Returns the next element in the list, if any.
    pub fn tail(&self) -> Option<&Self> {
        match self {
            Node::Root => None,
            Node::Head { tail, .. } => Some(tail),
        }
    }

    /// Returns the first data element in this list, if any.
    pub fn first(&self) -> Option<&T> {
        match self {
            Node::Root => None,
            Node::Head { data, .. } => Some(&data),
        }
    }

    /// Returns the length of this list.
    pub fn len(&self) -> usize {
        self.tail().map_or(0, |t| 1 + t.len())
    }

    /// Returns `true` if this list is empty.
    pub fn is_empty(&self) -> bool {
        match self {
            Node::Root => true,
            _ => false,
        }
    }

    /// Returns a sublist made by skipping the `n` first elements.
    ///
    /// Returns `None` if `n >= self.len()`.
    pub fn skip(&self, n: usize) -> Option<&Self> {
        match n {
            0 => Some(self),
            n => self.tail().and_then(|t| t.skip(n - 1)),
        }
    }

    /// Returns the data at index `n`.
    ///
    /// Returns `None` if `n >= self.len()`.
    pub fn get(&self, n: usize) -> Option<&T> {
        self.skip(n).and_then(Node::first)
    }

    /// Returns the data for the last item in this list.
    ///
    /// Returns `None` if `self` is empty.
    pub fn last(&self) -> Option<&T> {
        match self {
            Node::Root => None,
            Node::Head { data, tail } => Some(tail.last().unwrap_or(data)),
        }
    }

    /// Fold the given function over this list.
    ///
    /// Conceptually, runs the code:
    ///
    /// ```rust,ignore
    /// for data in self {
    ///     start = f(start, data);
    /// }
    /// start
    /// ```
    pub fn fold<F, S>(&self, start: S, mut f: F) -> S
    where
        F: FnMut(S, T) -> S,
        T: Clone,
    {
        match self {
            Node::Root => start,
            Node::Head { tail, data } => tail.fold(f(start, data.clone()), f),
        }
    }

    /// Reverse this list.
    ///
    /// This does not return a stacklist; instead, it runs `f` on a reversed version of `self`.
    pub fn reverse<F, R>(&self, f: F) -> R
    where
        F: for<'b> FnOnce(&'b Node<'b, T>) -> R,
        R: 'static,
        T: Clone,
    {
        fn reverse_inner<'b, T, F, R>(target: &Node<'b, T>, source: &Node<'b, T>, f: F) -> R
        where
            F: for<'c> FnOnce(&'c Node<'c, T>) -> R,
            R: 'static,
            T: Clone,
        {
            match source {
                Node::Root => f(target),
                Node::Head { data, tail } => reverse_inner(&target.prepend(data.clone()), tail, f),
            }
        }

        reverse_inner(&Node::Root, self, f)
    }

    /// Prepend all the elements from the given iterator, in reverse order.
    ///
    /// # Examples
    ///
    /// ```rust
    /// stack_list::stacklist!(let a = [3, 4, 5]);
    /// assert_eq!(a.get(0), Some(&3));
    ///
    /// a.prepend_all_rev([2, 1].iter().copied(), |b| {
    ///     assert_eq!(b.get(0), Some(&1));
    /// });
    /// ```
    pub fn prepend_all_rev<I, F, R>(&self, mut i: I, f: F) -> R
    where
        I: Iterator<Item = T>,
        F: for<'b> FnOnce(&'b Node<'b, T>) -> R,
        R: 'static,
    {
        match i.next() {
            None => f(self),
            Some(x) => self.prepend(x).prepend_all_rev(i, f),
        }
    }

    /// Prepend all the elements from the given iterator.
    ///
    /// # Examples
    ///
    /// ```rust
    /// stack_list::stacklist!(let a = [3, 4, 5]);
    /// assert_eq!(a.get(0), Some(&3));
    ///
    /// a.prepend_all([1, 2].iter().copied(), |b| {
    ///     assert_eq!(b.get(0), Some(&1));
    /// });
    /// ```
    pub fn prepend_all<I, F, R>(&self, i: I, f: F) -> R
    where
        I: DoubleEndedIterator<Item = T>,
        F: for<'b> FnOnce(&'b Node<'b, T>) -> R,
        R: 'static,
    {
        self.prepend_all_rev(i.rev(), f)
    }

    /// Build a stacklist using the items from the iterator in reverse order.
    ///
    /// Note: this does not return the stacklist. Instead, it calls the given closure
    /// with the generated list.
    pub fn from_rev_iterator<I, F, R>(i: I, f: F) -> R
    where
        I: Iterator<Item = T>,
        F: for<'b> FnOnce(&'b Node<'b, T>) -> R,
        R: 'static,
    {
        Node::prepend_all_rev(&Node::Root, i, f)
    }

    /// Build a stacklist using the items from the iterator.
    ///
    /// Note: this does not return the stacklist. Instead, it calls the given closure
    /// with the generated list.
    pub fn from_iterator<I, F, R>(i: I, f: F) -> R
    where
        I: DoubleEndedIterator<Item = T>,
        F: for<'b> FnOnce(&'b Node<'b, T>) -> R,
        R: 'static,
    {
        Node::from_rev_iterator(i.rev(), f)
    }
}

impl<'b, T> Iterator for &'b Node<'b, T> {
    type Item = &'b T;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Node::Root => None,
            Node::Head { data, tail } => {
                *self = tail;
                Some(&data)
            }
        }
    }
}
