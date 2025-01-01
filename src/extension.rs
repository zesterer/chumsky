//! Types and traits that let you write extensions for chumsky.
//!
//! Chumsky is a complicated crate that performs many internal optimizations to keep your parsers fast. These
//! optimizations mean that chumsky's core is rapidly changing, difficult to work with, and reveals a lot of
//! often-superfluous implementation details that are necessary to account for.
//!
//! In short: it's not a good basis for a stable public API upon which to build a parser ecosystem.
//!
//! To get around this problem, chumsky provides an extension interface (the contents of this module). This is a set of
//! types, traits, and functions that we've decided that we're comfortable providing long-term support for even if
//! the core of chumsky changes in an otherwise breaking manner in the future.
//!
//! The extension API is versioned. See the [`v1`] module for the current implementation of the API.
//!
//! # Example
//!
//! ```
//! use chumsky::{
//!     prelude::*,
//!     error::LabelError,
//!     input::InputRef,
//!     extension::v1::{ExtParser, Ext},
//!     DefaultExpected,
//! };
//!
//! // An example extension parser that expects a null byte.
//! pub struct Null_;
//!
//! // We implement `ExtParser` for our null byte parser, plugging us into the chumsky ecosystem
//! impl<'src, I, E> ExtParser<'src, I, (), E> for Null_
//! where
//!     I: Input<'src, Token = u8>,
//!     E: extra::ParserExtra<'src, I>,
//! {
//!     fn parse(&self, inp: &mut InputRef<'src, '_, I, E>) -> Result<(), E::Error> {
//!         let before = inp.cursor();
//!         match inp.next_maybe().as_deref() {
//!             // The next token was a null byte, meaning that parsing was successful
//!             Some(b'\0') => Ok(()),
//!             // The next token was something that wasn't a null byte, generate an error instead
//!             found => Err(LabelError::<I, _>::expected_found(
//!                 // Expected a null byte
//!                 [DefaultExpected::Token(b'\0'.into())],
//!                 // Found whatever the token was instead
//!                 found.copied().map(Into::into),
//!                 // The span of the error is the span of the token that was found instead
//!                 inp.span_since(&before),
//!             )),
//!         }
//!     }
//! }
//!
//! // Finally, we create an easy way to name the parser type for users
//! pub type Null = Ext<Null_>;
//!
//! // It's also conventional to create a function to conveniently use the parser primitive
//! pub fn null() -> Null {
//!     Ext(Null_)
//! }
//!
//! // Let's give our parser a test!
//! fn make_parser<'src>() -> impl Parser<'src, &'src [u8], ()> {
//!     null()
//! }
//!
//! assert_eq!(make_parser().parse(b"\0").into_result(), Ok(()));
//! assert!(make_parser().parse(b"!").has_errors());
//! assert!(make_parser().parse(b"").has_errors());
//! ```

use super::*;

/// Version 1 of the extension API.
///
/// Versioning the extension API allows us to make significant changes to it in the future without breaking crates that
/// depend on it.
pub mod v1 {
    pub use super::current::{Ext, ExtParser};
}

mod current {
    use super::*;

    /// A trait implemented by extension parsers.
    ///
    /// Implement this trait, and chumsky will automatically make [`Ext<YourParser>`] implement [`Parser`] for free.
    ///
    /// This trait is a stable interface that can be used to build on top of chumsky without exposing extension crates to
    /// the complex inner workings of chumsky, allowing us to iterate on the core to improve performance without regularly
    /// breaking the public API.
    ///
    /// If your parser is a combinator and you'd like it to be used like a method (such as chumsky's built-in `a.or(b)`
    /// combinator), it is recommended that you implement an extension trait in your own library and have users import
    /// it, like so:
    ///
    /// ```
    /// use chumsky::prelude::*;
    ///
    /// pub struct FrobnicatedWith<A, B> { a: A, b: B }
    ///
    /// pub trait ParserExt<'src, I, O, E>
    /// where
    ///     I: Input<'src>,
    ///     E: extra::ParserExtra<'src, I>
    /// {
    ///     fn frobnicated_with<B>(self, other: B) -> FrobnicatedWith<Self, B>
    ///     where
    ///         Self: Sized,
    ///         B: Parser<'src, I, O, E>,
    ///     {
    ///         FrobnicatedWith { a: self, b: other }
    ///     }
    /// }
    /// ```
    ///
    /// Now, users can import your trait and do `a.frobnicate_with(b)` as if your parser were native to chumsky!
    pub trait ExtParser<'src, I: Input<'src>, O, E: ParserExtra<'src, I>> {
        /// Attempt parsing on the given input.
        ///
        /// See [`InputRef`] for more information about how you can work with parser inputs.
        fn parse(&self, inp: &mut InputRef<'src, '_, I, E>) -> Result<O, E::Error>;

        /// Attempt to check the given input.
        ///
        /// This function should have **exactly** the same behavior as [`ExtParser::parse`]. If the behavior differs,
        /// the result of using the parser is unspecified (note that chumsky tries to aggressively avoid generating
        /// outputs if it doesn't use them, and will readily swap between [`ExtParser::parse`] and [`ExtParser::check`]
        /// when it thinks that doing so might yield performance benefits).
        ///
        /// By default, this method just uses `ExtParser::parse`, dropping the output. You may want to override the
        /// implementation so that this output is never even generated, thereby improving performance.
        fn check(&self, inp: &mut InputRef<'src, '_, I, E>) -> Result<(), E::Error> {
            self.parse(inp).map(|_| ())
        }
    }

    /// A type used to wrap parser extensions.
    ///
    /// Sadly, Rust's trait coherence rules (often called 'orphan rules') prevent us from having a blanket
    /// implementation of [`Parser`] for any implementer of [`ExtParser`]. This wrapper type is the compromise solution
    /// that keeps things working: wrap your parser types in [`Ext`], and you can start talking to the rest of the
    /// chumsky ecosystem. See [`extension`] for an example of how to do this.
    ///
    /// It's possible that future changes to Rust's coherence rules, or to chumsky's core, may relax this requirement in
    /// the future.
    ///
    /// If you're writing an extension crate for chumsky, you can make things less confusing for your users by putting your
    /// parser behind a type alias.
    #[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
    #[derive(Copy, Clone, Default, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    #[repr(transparent)]
    pub struct Ext<T: ?Sized>(pub T);

    impl<'src, I, O, E, P> Parser<'src, I, O, E> for Ext<P>
    where
        I: Input<'src>,
        E: ParserExtra<'src, I>,
        P: ExtParser<'src, I, O, E>,
    {
        #[inline(always)]
        fn go<M: Mode>(&self, inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, O> {
            let before = inp.cursor();
            match M::choose(&mut *inp, |inp| self.0.parse(inp), |inp| self.0.check(inp)) {
                Ok(out) => Ok(out),
                Err(err) => {
                    inp.add_alt_err(&before.inner, err);
                    Err(())
                }
            }
        }

        go_extra!(O);
    }
}
