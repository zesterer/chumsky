use super::*;

/// A helper trait for [`Stream`]. There is no need to implement this trait yourself, nor do you need to care about its
/// existence. It is marked as 'deprecated' to discourage its use and to indicate that it is not part of the crate's
/// semver guarantees.
#[deprecated(note = "This trait is excluded from the semver guarantees of chumsky. If you decide to use it, broken builds are your fault.")]
pub trait StreamExtend<T>: Iterator<Item = T> {
    /// Extend the vector with input. The actual amount can be more or less than `n`.
    fn extend(&mut self, v: &mut Vec<T>, n: usize);
}

#[allow(deprecated)]
impl<I: Iterator> StreamExtend<I::Item> for I {
    fn extend(&mut self, v: &mut Vec<I::Item>, n: usize) {
        v.reserve(n);
        v.extend(self.take(n));
    }
}

/// A utility type used to flatten input trees.
pub enum Flat<I, Iter> {
    /// The input tree flattens into a single input.
    Single(I),
    /// The input tree flattens into many sub-trees.
    Many(Iter),
}

/// A type that represents a stream of input tokens. Unlike [`Iterator`], this type supports backtracking and a few
/// other features required by the crate.
#[allow(deprecated)]
pub struct Stream<'a, I, S: Span, Iter: Iterator<Item = (I, S)> + ?Sized = dyn StreamExtend<(I, S)> + 'a> {
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

    /// Eagerly evaluate the token stream, returning an iterator over the tokens in it (but leaving the stream
    /// unaffected).
    ///
    /// This is most useful when you wish to check the input of a parser during debugging.
    pub fn fetch_tokens(&mut self) -> impl Iterator<Item = (I, S)> + '_ where (I, S): Clone {
        self.buffer.extend(&mut self.iter);
        self.buffer.iter().cloned()
    }
}

impl<'a, I: Clone, S: Span + 'a> BoxStream<'a, I, S> {
    /// Create a new `Stream` from an iterator of nested tokens and a function that flattens them.
    ///
    /// It's not uncommon for compilers to perform delimiter parsing during the lexing stage (rustc does this!). When
    /// this is done, the output of the lexing stage is usually a series of nested token trees. This functions allows
    /// you to easily flatten such token trees into a linear token stream so that they can be parsed by Chumsky.
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
    ///     Paren,
    ///     Brace,
    /// }
    ///
    /// // The structure of this token tree is very similar to that which Rust uses.
    /// // See: https://docs.rs/syn/0.11.1/syn/enum.TokenTree.html
    /// enum TokenTree {
    ///     Token(Token),
    ///     Tree(Delimiter, Vec<(TokenTree, Span)>),
    /// }
    ///
    /// fn flatten_tts(eoi: Span, token_trees: Vec<(TokenTree, Span)>) -> BoxStream<'static, Token, Span> {
    ///     use std::iter::once;
    ///     // Currently, this is quite an explicit process: it will likely become easier in subsequent versions of Chumsky.
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
        F: FnMut((P, S)) -> Flat<(I, S), Many> + 'a
    >(eoi: S, iter: Iter, mut flatten: F) -> Self {
        let mut v: Vec<std::collections::VecDeque<(P, S)>> = vec![iter.collect()];
        Self::from_iter(
            eoi,
            Box::new(std::iter::from_fn(move || loop {
                if let Some(many) = v.last_mut() {
                    match many.pop_front().map(&mut flatten) {
                        Some(Flat::Single(input)) => break Some(input),
                        Some(Flat::Many(many)) => v.push(many.collect()),
                        None => { v.pop(); },
                    }
                } else {
                    break None;
                }
            })),
        )
    }
}

impl<'a, I: Clone, S: Span> Stream<'a, I, S> {
    pub(crate) fn offset(&self) -> usize { self.offset }

    pub(crate) fn save(&self) -> usize { self.offset }
    pub(crate) fn revert(&mut self, offset: usize) { self.offset = offset; }

    fn pull_until(&mut self, offset: usize) -> Option<&(I, S)> {
        let additional = offset.saturating_sub(self.buffer.len()) + 1024;
        #[allow(deprecated)]
        self.iter.extend(&mut self.buffer, additional);
        self.buffer.get(offset)
    }

    pub(crate) fn next(&mut self) -> (usize, S, Option<I>) {
        match self.pull_until(self.offset).cloned() {
            Some((out, span)) => {
                self.offset += 1;
                (self.offset - 1, span, Some(out))
            },
            None => (self.offset, self.eoi.clone(), None),
        }
    }

    pub(crate) fn span_since(&mut self, start: usize) -> S {
        let start = self.pull_until(start)
            .as_ref()
            .map(|(_, s)| s.start())
            .unwrap_or_else(|| self.eoi.start());
        let end = self.pull_until(self.offset.saturating_sub(1))
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

    pub(crate) fn try_parse<O, E, F: FnOnce(&mut Self) -> PResult<I, O, E>>(&mut self, f: F) -> PResult<I, O, E> {
        self.attempt(move |stream| {
            let out = f(stream);
            (out.1.is_ok(), out)
        })
    }
}

impl<'a> From<&'a str> for Stream<'a, char, Range<usize>, Box<dyn Iterator<Item = (char, Range<usize>)> + 'a>> {
    /// Please note that Chumsky currently uses character indices and note byte offsets in this impl. This is likely to
    /// change in the future. If you wish to use byte offsets, you can do so with [`Stream::from_iter`].
    fn from(s: &'a str) -> Self {
        let len = s.chars().count();
        Self::from_iter(len..len + 1, Box::new(s.chars().enumerate().map(|(i, c)| (c, i..i + 1))))
    }
}

impl<'a, T: Clone> From<&'a [T]> for Stream<'a, T, Range<usize>, Box<dyn Iterator<Item = (T, Range<usize>)> + 'a>> {
    fn from(s: &'a [T]) -> Self {
        let len = s.len();
        Self::from_iter(len..len + 1, Box::new(s.iter().cloned().enumerate().map(|(i, x)| (x, i..i + 1))))
    }
}

impl<'a, T: Clone + 'a, const N: usize> From<[T; N]> for Stream<'a, T, Range<usize>, Box<dyn Iterator<Item = (T, Range<usize>)> + 'a>> {
    fn from(s: [T; N]) -> Self {
        let len = s.len();
        Self::from_iter(len..len + 1, Box::new(std::array::IntoIter::new(s).enumerate().map(|(i, x)| (x, i..i + 1))))
    }
}

// impl<'a, T: Clone, S: Clone + Span<Context = ()>> From<&'a [(T, S)]> for Stream<'a, T, S, Box<dyn Iterator<Item = (T, S)> + 'a>>
//     where S::Offset: Default
// {
//     fn from(s: &'a [(T, S)]) -> Self {
//         Self::from_iter(Default::default(), Box::new(s.iter().cloned()))
//     }
// }
