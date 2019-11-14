//! This library implements a heapless linked list by keeping each element on the stack.
//!
//! Compared to a most traditional lists, this has quite a few drawbacks:
//! * Not "self-contained": you cannot easily store a `Node` as a member like you would a
//!   `Vec`. To exist, a list needs to point to the next element, and so on until the end of the
//!   list. This is mostly fine in recursive calls, but can be a pain otherwise.
//! * Cannot easily be created with an arbitrary size. Instead, continuation-passing style is used:
//!   the generated list is given to a closure. See [`Node::from_iterator`] for instance.
//! * Not very memory-efficient compared to a Vec/Array: it stores at least one pointer per node
//!   (just like linked lists), and "dynamic" functions that use the continuation style may
//!   also insert function frames for each node.
//!
//! It has two main advantages:
//! * Compared to traditional containers, it does not need any heap allocation.
//! * Compared to "array-backed" containers, it can grow to arbitrary sizes.
//!
//! The primary purpose is to efficiently keep a context when traversing trees recursively.
//!
//! [`Node::from_iterator`]: Node::from_iterator()
//!
//! # Examples
//!
//! ```rust
//! // Make an initial stack list from a literal.
//! stack_list::make!(let l = [1, 2, 3, 4]);
//!
//! // We can iterate on the list (and collect it).
//! let v: Vec<_> = dbg!(l.iter().copied().collect());
//!
//! // We can also create a new list from an iterator
//! // Though instead of returning the value, it inserts it in the given closure.
//! stack_list::Node::from_iterator(v.iter(), |node| {
//!     println!("{:?}", node.skip(2));
//! });
//! ```
#![no_std]
#![deny(missing_docs)]

/// A stack-based linked list.
///
/// This is a node in a traditional linked list. The main difference is that it does not box the
/// next element, but simply points to it. As a result, it is harder to pass around or to mutate,
/// but has the advantage of not requiring any heap allocation.
///
/// It implements `Iterator`, so it gets a lot of functions for free from there.
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
/// This also only works with fixed-size literals known at compile-time. This will _not_ work with
/// a variable. You'll want something like [`Node::from_iterator`] instead.
///
/// [`Node::from_iterator`]: Node::from_iterator()
///
/// # Examples
///
/// ```rust
/// // This would desugar to something like:
/// // ```
/// // let _0 = stack_list::Node::Root;
/// // let _1 = _0.prepend(4);
/// // let _2 = _1.prepend(3);
/// // let _3 = _2.prepend(2);
/// // let my_list = _3.prepend(1);
/// // ```
/// stack_list::make!(let my_list = [1, 2, 3, 4]);
/// assert_eq!(my_list.len(), 4);
/// assert_eq!(my_list.get(3), Some(&4));
///
/// println!("{:?}", my_list);
/// ```
#[macro_export]
macro_rules! make {
    ( let $name:ident = [ $head:expr $(,)? ] ) => {
        let root = $crate::Node::Root;
        let $name = root.prepend($head);
    };
    ( let $name:ident = [ $head:expr , $($tail:expr),* ] ) => {
        $crate::make!(let n = [ $($tail),* ] );
        let $name = n.prepend($head);
    };
}

impl<'a, T> Default for Node<'a, T> {
    fn default() -> Self {
        Self::new()
    }
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
        if let Node::Head { ref data, ref tail } = *self {
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

    /// Reverse this list.
    ///
    /// This does not return a stacklist; instead, it runs `f` on a reversed version of `self`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use stack_list::Node;
    ///
    /// fn get_iterator() -> impl Iterator<Item=i32> {
    ///    (1..).skip_while(|&i| i < 7).map(|i| i*2).take(4)
    /// }
    ///
    /// // Combine `from_rev_iterator` and `reverse` to implement a poor man's `from_iterator`.
    /// let twenty = Node::from_rev_iterator(get_iterator(), |rl| {
    ///     rl.reverse(|l| {
    ///         *l.last().unwrap()
    ///     })
    /// });
    /// assert_eq!(twenty, 20);
    /// ```
    pub fn reverse<F, R>(&self, f: F) -> R
    where
        F: for<'b> FnOnce(&'b Node<'b, T>) -> R,
        R: 'static,
        T: Clone,
    {
        Node::from_rev_iterator(self.iter().cloned(), f)
    }

    /// Prepend all the elements from the given iterator, in reverse order.
    ///
    /// # Examples
    ///
    /// ```rust
    /// stack_list::make!(let a = [3, 4, 5]);
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
    /// stack_list::make!(let a = [3, 4, 5]);
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
    ///
    /// This function requires the iterator to be double-ended. This is the case for most iterators
    /// that come from slices, but if your iterator isn't double-ended, you may need to use
    /// [`from_rev_iterator`] and [`reverse`].
    ///
    /// [`from_rev_iterator`]: Node::from_rev_iterator()
    /// [`reverse`]: Node::reverse()
    ///
    /// # Examples
    ///
    /// ```rust
    /// use stack_list::Node;
    ///
    /// Node::from_iterator((1..10).into_iter().filter(|i| i % 3 == 0).map(|i| i*2), |l| {
    ///     assert_eq!(l.last(), Some(&18));
    /// });
    /// ```
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
