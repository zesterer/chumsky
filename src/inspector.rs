//! Parser extensions that inspect the input without modifying it.
//!
//! *"Only one man stood and watched the sky, stood with terrible sadness in his eyes
//! and rubber bungs in his ears. He knew exactly what was happening and had known
//! ever since his Sub-Etha Sens-O-Matic had started winking in the dead of night
//! beside his pillar and woken him with a start."*
use crate::{input::Marker, Input};
use core::ops::{Deref, DerefMut};

#[allow(unused)] // for intra-doc links
use crate::Parser;

/// A type that receives event hooks when certain parsing actions occur.
///
/// If you don't need to receive event hooks, use [`SimpleState`].
pub trait Inspector<'a, I: Input<'a>> {
    /// A type the Inspector can use to revert to a previous state.
    ///
    /// For implementation reasons, this is required to be `Copy + Clone`.
    type SaveMarker: Copy + Clone;

    /// This function is called when a new token is read from the input stream.
    // impl note: this should be called only when `self.offset` is updated, not when we only peek at the next token.
    fn on_token(&mut self, token: &I::Token);
    /// This function is called when a combinator saves the current state of the parse.
    fn on_save(&self, offset: I::Offset) -> Self::SaveMarker;
    /// This function is called when a combinator rewinds to an earlier state of the parser.
    ///
    /// You can use [`Marker::ext_checkpoint`] to get back the [`SaveMarker`][Self::SaveMarker]
    /// you originally created in [`on_save`][Self::on_save].
    fn on_rewind<'parse>(&mut self, marker: Marker<'a, 'parse, I, Self::SaveMarker>);
}

impl<'a, I: Input<'a>> Inspector<'a, I> for () {
    type SaveMarker = ();
    fn on_token(&mut self, _: &<I as Input<'a>>::Token) {}
    fn on_save(&self, _: <I as Input<'a>>::Offset) -> Self::SaveMarker {}
    fn on_rewind<'parse>(&mut self, _: Marker<'a, 'parse, I, Self>) {}
}

/// A state type that should be accessible directly from `parser.state()` and has no special behavior.
///
/// This wrapper implements the [`Inspector`] trait for you so you don't have to.
pub struct SimpleState<T>(pub T);
impl<'a, T, I: Input<'a>> Inspector<'a, I> for SimpleState<T> {
    type SaveMarker = ();
    fn on_token(&mut self, _: &<I as Input<'a>>::Token) {}
    fn on_save<'parse>(&self, _: <I as Input<'a>>::Offset) -> Self::SaveMarker {}
    fn on_rewind<'parse>(&mut self, _: Marker<'a, 'parse, I, Self::SaveMarker>) {}
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
