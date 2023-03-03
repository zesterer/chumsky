use core::ops::{Deref, DerefMut};

pub enum MaybeRef<'a, T> {
    Ref(&'a T),
    Own(T),
}

impl<'a, T> MaybeRef<'a, T> {
    pub fn new_own(val: T) -> MaybeRef<'a, T> {
        MaybeRef::Own(val)
    }

    pub fn new_ref(val: &'a T) -> MaybeRef<'a, T> {
        MaybeRef::Ref(val)
    }

    pub fn make_ref(&mut self) -> MaybeRef<'_, T> {
        match self {
            MaybeRef::Ref(r) => MaybeRef::Ref(*r),
            MaybeRef::Own(o) => MaybeRef::Ref(o),
        }
    }
}

impl<'a, T> Deref for MaybeRef<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        match self {
            MaybeRef::Ref(r) => &**r,
            MaybeRef::Own(o) => o
        }
    }
}

pub enum MaybeMut<'a, T> {
    Ref(&'a mut T),
    Own(T),
}

impl<'a, T> MaybeMut<'a, T> {
    pub fn new_own(val: T) -> MaybeMut<'a, T> {
        MaybeMut::Own(val)
    }

    pub fn new_ref(val: &'a mut T) -> MaybeMut<'a, T> {
        MaybeMut::Ref(val)
    }

    pub fn make_ref(&mut self) -> MaybeMut<'_, T> {
        match self {
            MaybeMut::Ref(r) => MaybeMut::Ref(*r),
            MaybeMut::Own(o) => MaybeMut::Ref(o),
        }
    }
}

impl<'a, T> Deref for MaybeMut<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        match self {
            MaybeMut::Ref(r) => &**r,
            MaybeMut::Own(o) => o
        }
    }
}

impl<'a, T> DerefMut for MaybeMut<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            MaybeMut::Ref(r) => *r,
            MaybeMut::Own(o) => o,
        }
    }
}
