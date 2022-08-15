use alloc::{string::String, vec::Vec};

mod private {
    pub trait Sealed<T> {}

    impl<T> Sealed<T> for T {}
    impl<T, A: Sealed<T>> Sealed<T> for (A, T) {}
    impl<T> Sealed<T> for Option<T> {}
    impl<T> Sealed<T> for alloc::vec::Vec<T> {}
    impl Sealed<char> for alloc::string::String {}
}

#[allow(clippy::len_without_is_empty)]
pub trait Chain<T>: private::Sealed<T> {
    fn len(&self) -> usize;
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
        v.extend(self);
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
