//! Parser extensions that inspect the input without modifying it.
//!
//! *"Only one man stood and watched the sky, stood with terrible sadness in his eyes
//! and rubber bungs in his ears. He knew exactly what was happening and had known
//! ever since his Sub-Etha Sens-O-Matic had started winking in the dead of night
//! beside his pillar and woken him with a start."*

use super::*;
use crate::input::{Checkpoint, Cursor};

/// A type that receives event hooks when certain parsing actions occur.
///
/// If you don't need to receive event hooks, use [`SimpleState`].
pub trait Inspector<'src, I: Input<'src>> {
    /// A type the Inspector can use to revert to a previous state.
    ///
    /// For implementation reasons, this is required to be `Copy + Clone`.
    type Checkpoint: Copy + Clone;

    /// This function is called when a new token is read from the input stream.
    // impl note: this should be called only when `self.cursor` is updated, not when we only peek at the next token.
    fn on_token(&mut self, token: &I::Token);
    /// This function is called when a combinator saves the current state of the parse.
    fn on_save<'parse>(&self, cursor: &Cursor<'src, 'parse, I>) -> Self::Checkpoint;
    /// This function is called when a combinator rewinds to an earlier state of the parser.
    ///
    /// You can use [`Checkpoint::inspector`] to get back the [`Checkpoint`][Self::Checkpoint]
    /// you originally created in [`on_save`][Self::on_save].
    fn on_rewind<'parse>(&mut self, marker: &Checkpoint<'src, 'parse, I, Self::Checkpoint>);
}

impl<'src, I: Input<'src>> Inspector<'src, I> for () {
    type Checkpoint = ();
    #[inline(always)]
    fn on_token(&mut self, _: &<I as Input<'src>>::Token) {}
    #[inline(always)]
    fn on_save<'parse>(&self, _: &Cursor<'src, 'parse, I>) -> Self::Checkpoint {}
    #[inline(always)]
    fn on_rewind<'parse>(&mut self, _: &Checkpoint<'src, 'parse, I, Self>) {}
}

/// A state type that should be accessible directly from `parser.state()` and has no special behavior.
///
/// This wrapper implements the [`Inspector`] trait for you so you don't have to.
pub struct SimpleState<T>(pub T);
impl<'src, T, I: Input<'src>> Inspector<'src, I> for SimpleState<T> {
    type Checkpoint = ();
    #[inline(always)]
    fn on_token(&mut self, _: &<I as Input<'src>>::Token) {}
    #[inline(always)]
    fn on_save<'parse>(&self, _: &Cursor<'src, 'parse, I>) -> Self::Checkpoint {}
    #[inline(always)]
    fn on_rewind<'parse>(&mut self, _: &Checkpoint<'src, 'parse, I, Self::Checkpoint>) {}
}

impl<T> Deref for SimpleState<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for SimpleState<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T> From<T> for SimpleState<T> {
    fn from(value: T) -> Self {
        Self(value)
    }
}
