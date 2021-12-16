mod private {
    pub trait Sealed<T> {}

    impl<T> Sealed<T> for T {}
    impl<T, A: Sealed<T>> Sealed<T> for (A, T) {}
    impl<T> Sealed<T> for Option<T> {}
    impl<T> Sealed<T> for Vec<T> {}
    impl Sealed<char> for String {}
}

/// A utility trait that facilitates chaining parser outputs together into [`Vec`]s.
///
/// See [`Parser::chain`](super::Parser).
#[allow(clippy::len_without_is_empty)]
pub trait Chain<T>: private::Sealed<T> {
    /// The number of items that this chain link consists of.
    fn len(&self) -> usize;
    /// Append the elements in this link to the chain.
    fn append_to(self, v: &mut Vec<T>);
}

impl<T> Chain<T> for T {
    fn len(&self) -> usize {
        1
    }
    fn append_to(self, v: &mut Vec<T>) {
        v.push(self);
    }
}

impl<T, A: Chain<T>> Chain<T> for (A, T) {
    fn len(&self) -> usize {
        1
    }
    fn append_to(self, v: &mut Vec<T>) {
        self.0.append_to(v);
        v.push(self.1);
    }
}

impl<T> Chain<T> for Option<T> {
    fn len(&self) -> usize {
        self.is_some() as usize
    }
    fn append_to(self, v: &mut Vec<T>) {
        if let Some(x) = self {
            v.push(x);
        }
    }
}

impl<T> Chain<T> for Vec<T> {
    fn len(&self) -> usize {
        self.as_slice().len()
    }
    fn append_to(mut self, v: &mut Vec<T>) {
        v.append(&mut self);
    }
}

impl Chain<char> for String {
    // TODO: Quite inefficient
    fn len(&self) -> usize {
        self.chars().count()
    }
    fn append_to(self, v: &mut Vec<char>) {
        v.extend(self.chars());
    }
}
