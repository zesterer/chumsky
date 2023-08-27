//! Traits and types that allow parsers to be cached between invocations.
//!
//! # Example
//!
//! ```
//! #![feature(lazy_cell)]
//! use std::sync::{LazyLock, Arc};
//! use chumsky::{prelude::*, cache::{Cache, Cached}};
//!
//! #[derive(Debug, PartialEq)]
//! enum Token<'a> { Ident(&'a str), Int(u64) }
//!
//! #[derive(Default)]
//! struct TokenParser;
//! impl Cached for TokenParser {
//!     type Parser<'a> = Arc<dyn Parser<'a, &'a str, Token<'a>, extra::Default> + Send + Sync + 'a>;
//!
//!     fn make_parser<'a>(self) -> Self::Parser<'a> {
//!         let ident = text::ident().map(Token::Ident);
//!         let num = text::int(10).from_str().unwrapped().map(Token::Int);
//!         Arc::new(ident.or(num))
//!     }
//! }
//!
//! // The parser cache doesn't have a lifetime and so can be stored pretty much anywhere:
//! static PARSER: LazyLock<Cache<TokenParser>> = LazyLock::new(Cache::default);
//!
//! // The parser can be used from any context simply by calling `.get()` on the cache
//! assert_eq!(PARSER.get().parse("42").into_result(), Ok(Token::Int(42)));
//! assert_eq!(PARSER.get().parse("hello").into_result(), Ok(Token::Ident("hello")));
//! ```

use super::*;

/// Implementing this trait allows you to cache parsers for use with inputs of different lifetimes, avoiding the
/// need to recreate the parser for each input lifetime.
pub trait Cached {
    /// The type of the parser to be cached.
    ///
    /// Because parsers tend to have unwieldy types, it is recommended to perform type erasure here. For example,
    /// a parser with input type `&'src str` and output type `Token<'src>` might have one of the following types.
    ///
    /// ```ignore
    /// Boxed<'src, 'src, &'src str, Token<'src>, extra::Default>
    /// Arc<dyn Parser<'src, &'src str, Token<'src>, extra::Default> + Send + Sync + 'src>
    /// ```
    type Parser<'src>;

    /// Create an instance of the parser
    fn make_parser<'src>(self) -> Self::Parser<'src>;
}

/// Allows a parser to be cached for reuse with inputs and outputs of different lifetimes.
pub struct Cache<C: Cached> {
    parser: C::Parser<'static>,
    #[allow(dead_code)]
    phantom: EmptyPhantom<C>,
}

impl<C: Cached + Default> Default for Cache<C> {
    fn default() -> Self {
        Self::new(C::default())
    }
}

impl<C: Cached> Cache<C> {
    /// Create a new cached parser.
    pub fn new(cacher: C) -> Self {
        Self {
            parser: cacher.make_parser(),
            phantom: EmptyPhantom::new(),
        }
    }

    /// Get a reference to the cached parser.
    ///
    /// Because this function is generic over an input lifetime, the returned parser can be used in many
    /// different contexts.
    pub fn get<'src>(&self) -> &C::Parser<'src> {
        // SAFETY: This is safe because the API of `Cache` requires that the parser we store is bound by an arbitrary
        // lifetime variable (see `Cached::make_parser`). Therefore, the implementor of `Cached` has no way to
        // 'discover' the lifetime and so, because lifetimes are entirely removed during monomorphisation, the parser
        // must be valid for arbitrary lifetimes.
        unsafe { &*(&self.parser as *const C::Parser<'_>).cast() }
    }
}
