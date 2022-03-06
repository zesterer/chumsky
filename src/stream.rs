//! Token streams and tools converting to and from them..
//!
//! *“What’s up?” “I don’t know,” said Marvin, “I’ve never been there.”*
//!
//! [`Stream`] is the primary type used to feed input data into a chumsky parser. You can create them in a number of
//! ways: from strings, iterators, arrays, etc.

use super::*;
use alloc::vec;

trait StreamExtend<T>: Iterator<Item = T> {
    /// Extend the vector with input. The actual amount can be more or less than `n`, but must be at least 1 (0 implies
    /// that the stream has been exhausted.
    fn extend(&mut self, v: &mut Vec<T>, n: usize);
}

#[allow(deprecated)]
impl<I: Iterator> StreamExtend<I::Item> for I {
    fn extend(&mut self, v: &mut Vec<I::Item>, n: usize) {
        v.reserve(n);
        v.extend(self.take(n));
    }
}

/// A utility type used to flatten input trees. See [`Stream::from_nested`].
pub enum Flat<I, Iter> {
    /// The input tree flattens into a single input.
    Single(I),
    /// The input tree flattens into many sub-trees.
    Many(Iter),
}

/// A type that represents a stream of input tokens. Unlike [`Iterator`], this type supports backtracking and a few
/// other features required by the crate.
#[allow(deprecated)]
pub struct Stream<
    'a,
    I,
    S: Span,
    Iter: Iterator<Item = (I, S)> + ?Sized = dyn Iterator<Item = (I, S)> + 'a,
> {
    pub(crate) phantom: PhantomData<&'a ()>,
    pub(crate) eoi: S,
    pub(crate) offset: usize,
    pub(crate) buffer: Vec<(I, S)>,
    pub(crate) iter: Iter,
}

/// A [`Stream`] that pulls tokens from a boxed [`Iterator`].
pub type BoxStream<'a, I, S> = Stream<'a, I, S, Box<dyn Iterator<Item = (I, S)> + 'a>>;

impl<'a, I, S: Span, Iter: Iterator<Item = (I, S)>> Stream<'a, I, S, Iter> {
    /// Create a new stream from an iterator of `(Token, Span)` pairs. A span representing the end of input must also
    /// be provided.
    ///
    /// There is no requirement that spans must map exactly to the position of inputs in the stream, but they should
    /// be non-overlapping and should appear in a monotonically-increasing order.
    pub fn from_iter(eoi: S, iter: Iter) -> Self {
        Self {
            phantom: PhantomData,
            eoi,
            offset: 0,
            buffer: Vec::new(),
            iter,
        }
    }

    /// Eagerly evaluate the token stream, returning an iterator over the tokens in it (but without modifying the
    /// stream's state so that it can still be used for parsing).
    ///
    /// This is most useful when you wish to check the input of a parser during debugging.
    pub fn fetch_tokens(&mut self) -> impl Iterator<Item = (I, S)> + '_
    where
        (I, S): Clone,
    {
        self.buffer.extend(&mut self.iter);
        self.buffer.iter().cloned()
    }
}

impl<'a, I: Clone, S: Span + 'a> BoxStream<'a, I, S> {
    /// Create a new `Stream` from an iterator of nested tokens and a function that flattens them.
    ///
    /// It's not uncommon for compilers to perform delimiter parsing during the lexing stage (Rust does this!). When
    /// this is done, the output of the lexing stage is usually a series of nested token trees. This functions allows
    /// you to easily flatten such token trees into a linear token stream so that they can be parsed (Chumsky currently
    /// only support parsing linear streams of inputs).
    ///
    /// For reference, [here](https://docs.rs/syn/0.11.1/syn/enum.TokenTree.html) is `syn`'s `TokenTree` type that it
    /// uses when parsing Rust syntax.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::{Stream, BoxStream, Flat};
    /// type Span = std::ops::Range<usize>;
    ///
    /// fn span_at(at: usize) -> Span { at..at + 1 }
    ///
    /// #[derive(Clone)]
    /// enum Token {
    ///     Local(String),
    ///     Int(i64),
    ///     Bool(bool),
    ///     Add,
    ///     Sub,
    ///     OpenParen,
    ///     CloseParen,
    ///     OpenBrace,
    ///     CloseBrace,
    ///     // etc.
    /// }
    ///
    /// enum Delimiter {
    ///     Paren, // ( ... )
    ///     Brace, // { ... }
    /// }
    ///
    /// // The structure of this token tree is very similar to that which Rust uses.
    /// // See: https://docs.rs/syn/0.11.1/syn/enum.TokenTree.html
    /// enum TokenTree {
    ///     Token(Token),
    ///     Tree(Delimiter, Vec<(TokenTree, Span)>),
    /// }
    ///
    /// // A function that turns a series of nested token trees into a linear stream that can be used for parsing.
    /// fn flatten_tts(eoi: Span, token_trees: Vec<(TokenTree, Span)>) -> BoxStream<'static, Token, Span> {
    ///     use std::iter::once;
    ///     // Currently, this is quite an explicit process: it will likely become easier in future versions of Chumsky.
    ///     Stream::from_nested(
    ///         eoi,
    ///         token_trees.into_iter(),
    ///         |(tt, span)| match tt {
    ///             // For token trees that contain just a single token, no flattening needs to occur!
    ///             TokenTree::Token(token) => Flat::Single((token, span)),
    ///             // Flatten a parenthesised token tree into an iterator of the inner token trees, surrounded by parenthesis tokens
    ///             TokenTree::Tree(Delimiter::Paren, tree) => Flat::Many(once((TokenTree::Token(Token::OpenParen), span_at(span.start)))
    ///                 .chain(tree.into_iter())
    ///                 .chain(once((TokenTree::Token(Token::CloseParen), span_at(span.end - 1))))),
    ///             // Flatten a braced token tree into an iterator of the inner token trees, surrounded by brace tokens
    ///             TokenTree::Tree(Delimiter::Brace, tree) => Flat::Many(once((TokenTree::Token(Token::OpenBrace), span_at(span.start)))
    ///                 .chain(tree.into_iter())
    ///                 .chain(once((TokenTree::Token(Token::CloseBrace), span_at(span.end - 1))))),
    ///         }
    ///     )
    /// }
    /// ```
    pub fn from_nested<
        P: 'a,
        Iter: Iterator<Item = (P, S)>,
        Many: Iterator<Item = (P, S)>,
        F: FnMut((P, S)) -> Flat<(I, S), Many> + 'a,
    >(
        eoi: S,
        iter: Iter,
        mut flatten: F,
    ) -> Self {
        let mut v: Vec<alloc::collections::VecDeque<(P, S)>> = vec![iter.collect()];
        Self::from_iter(
            eoi,
            Box::new(core::iter::from_fn(move || loop {
                if let Some(many) = v.last_mut() {
                    match many.pop_front().map(&mut flatten) {
                        Some(Flat::Single(input)) => break Some(input),
                        Some(Flat::Many(many)) => v.push(many.collect()),
                        None => {
                            v.pop();
                        }
                    }
                } else {
                    break None;
                }
            })),
        )
    }
}

impl<'a, I: Clone, S: Span> Stream<'a, I, S> {
    pub(crate) fn offset(&self) -> usize {
        self.offset
    }

    pub(crate) fn save(&self) -> usize {
        self.offset
    }
    pub(crate) fn revert(&mut self, offset: usize) {
        self.offset = offset;
    }

    fn pull_until(&mut self, offset: usize) -> Option<&(I, S)> {
        let additional = offset.saturating_sub(self.buffer.len()) + 1024;
        #[allow(deprecated)]
        (&mut &mut self.iter as &mut dyn StreamExtend<_>).extend(&mut self.buffer, additional);
        self.buffer.get(offset)
    }

    pub(crate) fn skip_if(&mut self, f: impl FnOnce(&I) -> bool) -> bool {
        match self.pull_until(self.offset).cloned() {
            Some((out, _)) if f(&out) => {
                self.offset += 1;
                true
            }
            Some(_) => false,
            None => false,
        }
    }

    pub(crate) fn next(&mut self) -> (usize, S, Option<I>) {
        match self.pull_until(self.offset).cloned() {
            Some((out, span)) => {
                self.offset += 1;
                (self.offset - 1, span, Some(out))
            }
            None => (self.offset, self.eoi.clone(), None),
        }
    }

    pub(crate) fn span_since(&mut self, start_offset: usize) -> S {
        debug_assert!(
            start_offset <= self.offset,
            "{} > {}",
            self.offset,
            start_offset
        );
        let start = self
            .pull_until(start_offset)
            .as_ref()
            .map(|(_, s)| s.start())
            .unwrap_or_else(|| self.eoi.start());
        let end = self
            .pull_until(self.offset.saturating_sub(1).max(start_offset))
            .as_ref()
            .map(|(_, s)| s.end())
            .unwrap_or_else(|| self.eoi.end());
        S::new(self.eoi.context(), start..end)
    }

    pub(crate) fn attempt<R, F: FnOnce(&mut Self) -> (bool, R)>(&mut self, f: F) -> R {
        let old_offset = self.offset;
        let (commit, out) = f(self);
        if !commit {
            self.offset = old_offset;
        }
        out
    }

    pub(crate) fn try_parse<O, E, F: FnOnce(&mut Self) -> PResult<I, O, E>>(
        &mut self,
        f: F,
    ) -> PResult<I, O, E> {
        self.attempt(move |stream| {
            let out = f(stream);
            (out.1.is_ok(), out)
        })
    }
}

impl<'a> From<&'a str>
    for Stream<'a, char, Range<usize>, Box<dyn Iterator<Item = (char, Range<usize>)> + 'a>>
{
    /// Please note that Chumsky currently uses character indices and not byte offsets in this impl. This is likely to
    /// change in the future. If you wish to use byte offsets, you can do so with [`Stream::from_iter`].
    fn from(s: &'a str) -> Self {
        let len = s.chars().count();
        Self::from_iter(
            len..len,
            Box::new(s.chars().enumerate().map(|(i, c)| (c, i..i + 1))),
        )
    }
}

impl<'a> From<String>
    for Stream<'a, char, Range<usize>, Box<dyn Iterator<Item = (char, Range<usize>)>>>
{
    /// Please note that Chumsky currently uses character indices and not byte offsets in this impl. This is likely to
    /// change in the future. If you wish to use byte offsets, you can do so with [`Stream::from_iter`].
    fn from(s: String) -> Self {
        let chars = s.chars().collect::<Vec<_>>();
        Self::from_iter(
            chars.len()..chars.len(),
            Box::new(chars.into_iter().enumerate().map(|(i, c)| (c, i..i + 1))),
        )
    }
}

impl<'a, T: Clone> From<&'a [T]>
    for Stream<'a, T, Range<usize>, Box<dyn Iterator<Item = (T, Range<usize>)> + 'a>>
{
    fn from(s: &'a [T]) -> Self {
        let len = s.len();
        Self::from_iter(
            len..len,
            Box::new(s.iter().cloned().enumerate().map(|(i, x)| (x, i..i + 1))),
        )
    }
}

impl<'a, T: Clone + 'a> From<Vec<T>>
    for Stream<'a, T, Range<usize>, Box<dyn Iterator<Item = (T, Range<usize>)> + 'a>>
{
    fn from(s: Vec<T>) -> Self {
        let len = s.len();
        Self::from_iter(
            len..len,
            Box::new(s.into_iter().enumerate().map(|(i, x)| (x, i..i + 1))),
        )
    }
}

impl<'a, T: Clone + 'a, const N: usize> From<[T; N]>
    for Stream<'a, T, Range<usize>, Box<dyn Iterator<Item = (T, Range<usize>)> + 'a>>
{
    fn from(s: [T; N]) -> Self {
        Self::from_iter(
            N..N,
            Box::new(
                core::array::IntoIter::new(s)
                    .enumerate()
                    .map(|(i, x)| (x, i..i + 1)),
            ),
        )
    }
}

impl<'a, T: Clone, const N: usize> From<&'a [T; N]>
    for Stream<'a, T, Range<usize>, Box<dyn Iterator<Item = (T, Range<usize>)> + 'a>>
{
    fn from(s: &'a [T; N]) -> Self {
        Self::from_iter(
            N..N,
            Box::new(s.iter().cloned().enumerate().map(|(i, x)| (x, i..i + 1))),
        )
    }
}

// impl<'a, T: Clone, S: Clone + Span<Context = ()>> From<&'a [(T, S)]> for Stream<'a, T, S, Box<dyn Iterator<Item = (T, S)> + 'a>>
//     where S::Offset: Default
// {
//     fn from(s: &'a [(T, S)]) -> Self {
//         Self::from_iter(Default::default(), Box::new(s.iter().cloned()))
//     }
// }
