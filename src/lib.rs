#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Node<'a, T> {
    Root,
    Head { data: T, tail: &'a Node<'a, T> },
}

#[macro_export]
macro_rules! stacklist {
    ( let $name:ident = [ $head:expr $(,)? ] ) => {
        let root = $crate::Node::Root;
        let $name = root.append($head);
    };
    ( let $name:ident = [ $head:expr , $($tail:expr),* ] ) => {
        $crate::stacklist!(let n = [ $($tail),* ] );
        let $name = n.append($head);
    };
}

impl<'a, T> Node<'a, T> {
    pub fn append(&'a self, data: T) -> Self {
        Node::Head { data, tail: self }
    }

    pub fn iter(&'a self) -> impl Iterator<Item = &'a T> {
        self
    }

    pub fn tail(&self) -> Option<&Self> {
        match self {
            Node::Root => None,
            Node::Head { tail, .. } => Some(tail),
        }
    }

    pub fn len(&self) -> usize {
        self.tail().map_or(0, |t| 1 + t.len())
    }

    pub fn nth(&self, n: usize) -> Option<&Self> {
        match n {
            0 => Some(self),
            n => self.tail().and_then(|t| t.nth(n - 1)),
        }
    }

    pub fn last(&self) -> &Self {
        self.tail().map_or(self, |t| t.last())
    }

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
                Node::Head { data, tail } => reverse_inner(&target.append(data.clone()), tail, f),
            }
        }

        reverse_inner(&Node::Root, self, f)
    }

    pub fn extend<I, F, R>(&self, mut i: I, f: F) -> R
    where
        I: Iterator<Item = T>,
        F: for<'b> FnOnce(&'b Node<'b, T>) -> R,
        R: 'static,
    {
        match i.next() {
            None => f(self),
            Some(x) => self.append(x).extend(i, f),
        }
    }

    pub fn from_iterator<I, F, R>(i: I, f: F) -> R
    where
        I: Iterator<Item = T>,
        F: for<'b> FnOnce(&'b Node<'b, T>) -> R,
        R: 'static,
    {
        Node::extend(&Node::Root, i, f)
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
