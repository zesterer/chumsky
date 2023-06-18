//! Utilities for chumsky.
#![no_std]

use core::marker::PhantomData;

/// A type that allows mentioning type parameters *without* all of the customary omission of auto traits that comes
/// with `PhantomData`.
pub struct EmptyPhantom<T>(PhantomData<T>);

impl<T> EmptyPhantom<T> {
    /// Create a new instance.
    pub const fn new() -> Self {
        Self(PhantomData)
    }
}

impl<T> Copy for EmptyPhantom<T> {}

impl<T> Clone for EmptyPhantom<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Default for EmptyPhantom<T> {
    fn default() -> Self {
        Self::new()
    }
}

// SAFETY: This is safe because `EmptyPhantom` doesn't actually contain a `T`.
unsafe impl<T> Send for EmptyPhantom<T> {}

// SAFETY: This is safe because `EmptyPhantom` doesn't actually contain a `T`.
unsafe impl<T> Sync for EmptyPhantom<T> {}

impl<T> Unpin for EmptyPhantom<T> {}

impl<T> core::panic::UnwindSafe for EmptyPhantom<T> {}

impl<T> core::panic::RefUnwindSafe for EmptyPhantom<T> {}
