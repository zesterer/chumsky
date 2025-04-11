//! Utility items used throughout the crate.

use super::*;

use core::hash::Hasher;

/// A value that may be a `T` or a mutable reference to a `T`.
pub type MaybeMut<'a, T> = Maybe<T, &'a mut T>;

/// A value that may be a `T` or a shared reference to a `T`.
pub type MaybeRef<'a, T> = Maybe<T, &'a T>;

/// A type that can represent a borrowed reference to a `T` or a value of `T`.
///
/// Used internally to facilitate zero-copy manipulation of tokens during error generation (see [`Error`]).
#[derive(Copy, Clone)]
pub enum Maybe<T, R: Deref<Target = T>> {
    /// We have a reference to `T`.
    Ref(R),
    /// We have a value of `T`.
    Val(T),
}

impl<T: PartialEq, R: Deref<Target = T>> PartialEq for Maybe<T, R> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        **self == **other
    }
}

impl<T: Eq, R: Deref<Target = T>> Eq for Maybe<T, R> {}

impl<T: PartialOrd, R: Deref<Target = T>> PartialOrd for Maybe<T, R> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        (**self).partial_cmp(&**other)
    }
}

impl<T: Ord, R: Deref<Target = T>> Ord for Maybe<T, R> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        (**self).cmp(&**other)
    }
}

impl<T: Hash, R: Deref<Target = T>> Hash for Maybe<T, R> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        T::hash(&**self, state)
    }
}

impl<T: fmt::Debug, R: Deref<Target = T>> fmt::Debug for Maybe<T, R> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        T::fmt(&**self, f)
    }
}

impl<T, R: Deref<Target = T>> Maybe<T, R> {
    /// Convert this [`Maybe<T, _>`] into a `T`, cloning the inner value if necessary.
    #[inline]
    pub fn into_inner(self) -> T
    where
        T: Clone,
    {
        match self {
            Self::Ref(x) => x.clone(),
            Self::Val(x) => x,
        }
    }

    /// Convert this [`Maybe<T, _>`] into an owned version of itself, cloning the inner reference if required.
    #[inline]
    pub fn into_owned<U>(self) -> Maybe<T, U>
    where
        T: Clone,
        U: Deref<Target = T>,
    {
        Maybe::Val(self.into_inner())
    }
}

impl<T, R: Deref<Target = T>> Deref for Maybe<T, R> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        match self {
            Self::Ref(x) => x,
            Self::Val(x) => x,
        }
    }
}

impl<T, R: DerefMut<Target = T>> DerefMut for Maybe<T, R> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            Self::Ref(x) => &mut *x,
            Self::Val(x) => x,
        }
    }
}

impl<T> From<T> for Maybe<T, &T> {
    #[inline]
    fn from(x: T) -> Self {
        Self::Val(x)
    }
}

impl<T> From<T> for Maybe<T, &mut T> {
    #[inline]
    fn from(x: T) -> Self {
        Self::Val(x)
    }
}

impl<'a, T> From<&'a T> for Maybe<T, &'a T> {
    #[inline]
    fn from(x: &'a T) -> Self {
        Self::Ref(x)
    }
}

impl<'a, T> From<&'a mut T> for Maybe<T, &'a mut T> {
    #[inline]
    fn from(x: &'a mut T) -> Self {
        Self::Ref(x)
    }
}

#[cfg(feature = "serde")]
impl<T: Serialize, R: Deref<Target = T>> Serialize for Maybe<T, R> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_newtype_struct("Maybe", &**self)
    }
}

#[cfg(feature = "serde")]
impl<'de, T: Deserialize<'de>, R: Deref<Target = T>> Deserialize<'de> for Maybe<T, R> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct MaybeVisitor<T, R>(PhantomData<(T, R)>);

        impl<'de2, T: Deserialize<'de2>, R: Deref<Target = T>> Visitor<'de2> for MaybeVisitor<T, R> {
            type Value = Maybe<T, R>;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                write!(formatter, "a Maybe")
            }

            fn visit_newtype_struct<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
            where
                D: Deserializer<'de2>,
            {
                T::deserialize(deserializer).map(Maybe::Val)
            }
        }

        deserializer.deserialize_newtype_struct("Maybe", MaybeVisitor(PhantomData))
    }
}

mod ref_or_val_sealed {
    pub trait Sealed<T> {}
}

/// An trait that allows abstracting over values of or references to a `T`.
///
/// Some [`Input`]s can only generate tokens by-reference (like `&[T]` -> `&T`), and some can only generate tokens
/// by-value (like `&str` -> `char`). This trait allows chumsky to handle both kinds of input.
///
/// The trait is sealed: you cannot implement it yourself.
pub trait IntoMaybe<'src, T: 'src>:
    ref_or_val_sealed::Sealed<T> + Borrow<T> + Into<MaybeRef<'src, T>>
{
    /// Project the referential properties of this type on to another type.
    ///
    /// For example, `<&Foo>::Proj<Bar> = &Bar` but `<Foo>::Proj<Bar> = Bar`.
    #[doc(hidden)]
    type Proj<U: 'src>: IntoMaybe<'src, U>;

    #[doc(hidden)]
    fn map_maybe<R: 'src>(
        self,
        f: impl FnOnce(&'src T) -> &'src R,
        g: impl FnOnce(T) -> R,
    ) -> Self::Proj<R>;
}

impl<T> ref_or_val_sealed::Sealed<T> for &T {}
impl<'src, T> IntoMaybe<'src, T> for &'src T {
    type Proj<U: 'src> = &'src U;
    fn map_maybe<R: 'src>(
        self,
        f: impl FnOnce(&'src T) -> &'src R,
        _g: impl FnOnce(T) -> R,
    ) -> Self::Proj<R> {
        f(self)
    }
}

impl<T> ref_or_val_sealed::Sealed<T> for T {}
impl<'src, T: 'src> IntoMaybe<'src, T> for T {
    type Proj<U: 'src> = U;
    fn map_maybe<R: 'src>(
        self,
        _f: impl FnOnce(&'src T) -> &'src R,
        g: impl FnOnce(T) -> R,
    ) -> Self::Proj<R> {
        g(self)
    }
}
