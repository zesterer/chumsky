//! Traits that allow chaining parser outputs together.
//!
//! *“And what’s happened to the Earth?” “Ah. It’s been demolished.” “Has it,” said Arthur levelly. “Yes. It just
//! boiled away into space.” “Look,” said Arthur, “I’m a bit upset about that.”*
//!
//! You usually don't need to interact with this trait, or even import it. It's only public so that you can see which
//! types implement it. See [`Parser::chain`](super::Parser) for examples of its usage.

use alloc::{string::String, vec::Vec};

mod private {
    use super::*;

    pub trait Sealed<T> {}

    impl<T> Sealed<T> for T {}
    impl<T, A: Sealed<T>> Sealed<T> for (A, T) {}
    impl<T> Sealed<T> for Option<T> {}
    impl<T> Sealed<T> for Vec<T> {}
    impl<T> Sealed<T> for Option<Vec<T>> {}
    impl<T> Sealed<T> for Vec<Option<T>> {}
    impl<T, A: Sealed<T>> Sealed<T> for Vec<(A, T)> {}
    impl Sealed<char> for String {}
    impl Sealed<char> for Option<String> {}
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

impl<T> Chain<T> for Option<Vec<T>> {
    fn len(&self) -> usize {
        self.as_ref().map_or(0, Chain::<T>::len)
    }
    fn append_to(self, v: &mut Vec<T>) {
        if let Some(x) = self {
            x.append_to(v);
        }
    }
}

impl Chain<char> for Option<String> {
    fn len(&self) -> usize {
        self.as_ref().map_or(0, Chain::<char>::len)
    }
    fn append_to(self, v: &mut Vec<char>) {
        if let Some(x) = self {
            x.append_to(v);
        }
    }
}

impl<T> Chain<T> for Vec<Option<T>> {
    fn len(&self) -> usize {
        self.iter().map(Chain::<T>::len).sum()
    }
    fn append_to(self, v: &mut Vec<T>) {
        self
            .into_iter()
            .for_each(|x| x.append_to(v));
    }
}

impl<T, A: Chain<T>> Chain<T> for Vec<(A, T)> {
    fn len(&self) -> usize {
        self.iter().map(Chain::<T>::len).sum()
    }
    fn append_to(self, v: &mut Vec<T>) {
        self
            .into_iter()
            .for_each(|x| x.append_to(v));
    }
}
