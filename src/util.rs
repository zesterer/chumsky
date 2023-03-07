use super::*;

use core::{
    cmp::{Ord, PartialEq, PartialOrd},
    hash::{Hash, Hasher},
    ops::{Deref, DerefMut},
};

pub(crate) type MaybeMut<'a, T> = Maybe<T, &'a mut T>;

pub type MaybeRef<'a, T> = Maybe<T, &'a T>;

/// A type that can represent a borrowed reference to a `T` or a value of `T`.
///
/// Used internally to faciltitate zero-copy manipulation of tokens during error generation (see [`Error`]).
#[derive(Copy, Clone)]
pub enum Maybe<T, R: Deref<Target = T>> {
    /// We have a reference to `T`.
    Ref(R),
    /// We have a value of `T`.
    Val(T),
}

impl<T: PartialEq, R: Deref<Target = T>> PartialEq for Maybe<T, R> {
    fn eq(&self, other: &Self) -> bool {
        &**self == &**other
    }
}

impl<T: Eq, R: Deref<Target = T>> Eq for Maybe<T, R> {}

impl<T: PartialOrd, R: Deref<Target = T>> PartialOrd for Maybe<T, R> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        (**self).partial_cmp(&**other)
    }
}

impl<T: Ord, R: Deref<Target = T>> Ord for Maybe<T, R> {
    fn cmp(&self, other: &Self) -> Ordering {
        (**self).cmp(&**other)
    }
}

impl<T: Hash, R: Deref<Target = T>> Hash for Maybe<T, R> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        T::hash(&**self, state)
    }
}

impl<T: fmt::Debug, R: Deref<Target = T>> fmt::Debug for Maybe<T, R> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        T::fmt(&**self, f)
    }
}

impl<T, R: Deref<Target = T>> Maybe<T, R> {
    /// Convert this [`MaybeRef<T>`] into a `T`, cloning the inner value if necessary.
    pub fn into_inner(self) -> T
    where
        T: Clone,
    {
        match self {
            Self::Ref(x) => x.clone(),
            Self::Val(x) => x,
        }
    }
}

impl<'a, T> Maybe<T, &'a T> {
    /// Convert this [`MaybeRef<T>`] into an owned version of itself, cloning the inner reference if required.
    pub fn into_owned<'b>(self) -> Maybe<T, &'b T>
    where
        T: Clone,
    {
        MaybeRef::Val(self.into_inner())
    }
}

impl<T, R: Deref<Target = T>> Deref for Maybe<T, R> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        match self {
            Self::Ref(x) => &*x,
            Self::Val(x) => x,
        }
    }
}

impl<T, R: DerefMut<Target = T>> DerefMut for Maybe<T, R> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            Self::Ref(x) => &mut *x,
            Self::Val(x) => x,
        }
    }
}

impl<'a, T> From<T> for Maybe<T, &'a T> {
    fn from(x: T) -> Self {
        Self::Val(x)
    }
}

impl<'a, T> From<&'a T> for Maybe<T, &'a T> {
    fn from(x: &'a T) -> Self {
        Self::Ref(x)
    }
}
