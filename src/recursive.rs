//! Recursive parsers (parser that include themselves within their patterns).
//!
//! *“It's unpleasantly like being drunk."
//! "What's so unpleasant about being drunk?"
//! "You ask a glass of water.”*
//!
//! The [`recursive()`] function covers most cases, but sometimes it's necessary to manually control the declaration and
//! definition of parsers more carefully, particularly for mutually-recursive parsers. In such cases, the functions on
//! [`Recursive`] allow for this.

use super::*;

#[cfg(not(feature = "sync"))]
struct OnceCell<T>(core::cell::Cell<Option<T>>);
#[cfg(not(feature = "sync"))]
impl<T> OnceCell<T> {
    pub fn new() -> Self {
        Self(core::cell::Cell::new(None))
    }
    pub fn set(&self, x: T) -> Result<(), ()> {
        // SAFETY: Function is not reentrant so we have exclusive access to the inner data
        unsafe {
            let vacant = (*self.0.as_ptr()).is_none();
            if vacant {
                self.0.as_ptr().write(Some(x));
                Ok(())
            } else {
                Err(())
            }
        }
    }
    #[inline]
    pub fn get(&self) -> Option<&T> {
        // SAFETY: We ensure that we never insert twice (so the inner `T` always lives as long as us, if it exists) and
        // neither function is possibly reentrant so there's no way we can invalidate mut xor shared aliasing
        unsafe { (*self.0.as_ptr()).as_ref() }
    }
}

#[cfg(feature = "sync")]
struct OnceCell<T>(spin::once::Once<T>);
#[cfg(feature = "sync")]
impl<T> OnceCell<T> {
    pub fn new() -> Self {
        Self(spin::once::Once::new())
    }
    pub fn set(&self, x: T) -> Result<(), ()> {
        // TODO: Race condition here, possibility of `Err(())` not being returned even through once is already occupied
        // We don't care enough about this right now to do anything though, it's not a safety violation
        if !self.0.is_completed() {
            self.0.call_once(move || x);
            Ok(())
        } else {
            Err(())
        }
    }
    #[inline]
    pub fn get(&self) -> Option<&T> {
        self.0.get()
    }
}

// TODO: Ensure that this doesn't produce leaks
enum RecursiveInner<T: ?Sized> {
    Owned(RefC<T>),
    Unowned(RefW<T>),
}

/// Type for recursive parsers that are defined through a call to `recursive`, and as such
/// need no internal indirection
pub type Direct<'a, 'b, I, O, Extra> = DynParser<'a, 'b, I, O, Extra>;

/// Type for recursive parsers that are defined through a call to [`Recursive::declare`], and as
/// such require an additional layer of allocation.
pub struct Indirect<'a, 'b, I: Input<'a>, O, Extra: ParserExtra<'a, I>> {
    inner: OnceCell<Box<DynParser<'a, 'b, I, O, Extra>>>,
}

/// A parser that can be defined in terms of itself by separating its [declaration](Recursive::declare) from its
/// [definition](Recursive::define).
///
/// Prefer to use [`recursive()`], which exists as a convenient wrapper around both operations, if possible.
pub struct Recursive<P: ?Sized> {
    inner: RecursiveInner<P>,
}

impl<'a, 'b, I: Input<'a>, O, E: ParserExtra<'a, I>> Recursive<Indirect<'a, 'b, I, O, E>> {
    /// Declare the existence of a recursive parser, allowing it to be used to construct parser combinators before
    /// being fulled defined.
    ///
    /// Declaring a parser before defining it is required for a parser to reference itself.
    ///
    /// This should be followed by **exactly one** call to the [`Recursive::define`] method prior to using the parser
    /// for parsing (i.e: via the [`Parser::parse`] method or similar).
    ///
    /// Prefer to use [`recursive()`], which is a convenient wrapper around this method and [`Recursive::define`], if
    /// possible.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// #[derive(Debug, PartialEq)]
    /// enum Chain {
    ///     End,
    ///     Link(char, Box<Chain>),
    /// }
    ///
    /// // Declare the existence of the parser before defining it so that it can reference itself
    /// let mut chain = Recursive::declare();
    ///
    /// // Define the parser in terms of itself.
    /// // In this case, the parser parses a right-recursive list of '+' into a singly linked list
    /// chain.define(just::<_, _, extra::Err<Simple<char>>>('+')
    ///     .then(chain.clone())
    ///     .map(|(c, chain)| Chain::Link(c, Box::new(chain)))
    ///     .or_not()
    ///     .map(|chain| chain.unwrap_or(Chain::End)));
    ///
    /// assert_eq!(chain.parse("").into_result(), Ok(Chain::End));
    /// assert_eq!(
    ///     chain.parse("++").into_result(),
    ///     Ok(Chain::Link('+', Box::new(Chain::Link('+', Box::new(Chain::End))))),
    /// );
    /// ```
    pub fn declare() -> Self {
        Recursive {
            inner: RecursiveInner::Owned(RefC::new(Indirect {
                inner: OnceCell::new(),
            })),
        }
    }

    /// Defines the parser after declaring it, allowing it to be used for parsing.
    // INFO: Clone bound not actually needed, but good to be safe for future compat
    #[track_caller]
    pub fn define<P: Parser<'a, I, O, E> + Clone + MaybeSync + 'b>(&mut self, parser: P) {
        let location = *Location::caller();
        self.parser()
            .inner
            .set(Box::new(parser))
            .unwrap_or_else(|_| {
                panic!("recursive parsers can only be defined once, trying to redefine it at {location}")
            });
    }
}

impl<P: ?Sized> Recursive<P> {
    #[inline]
    fn parser(&self) -> RefC<P> {
        match &self.inner {
            RecursiveInner::Owned(x) => x.clone(),
            RecursiveInner::Unowned(x) => x
                .upgrade()
                .expect("Recursive parser used before being defined"),
        }
    }

    fn weak(&self) -> Self {
        Self {
            inner: match &self.inner {
                RecursiveInner::Owned(x) => RecursiveInner::Unowned(RefC::downgrade(x)),
                RecursiveInner::Unowned(x) => RecursiveInner::Unowned(x.clone()),
            },
        }
    }
}

impl<P: ?Sized> Clone for Recursive<P> {
    fn clone(&self) -> Self {
        Self {
            inner: match &self.inner {
                RecursiveInner::Owned(x) => RecursiveInner::Owned(x.clone()),
                RecursiveInner::Unowned(x) => RecursiveInner::Unowned(x.clone()),
            },
        }
    }
}

#[cfg(feature = "stacker")]
#[inline]
pub(crate) fn recurse<R, F: FnOnce() -> R>(f: F) -> R {
    stacker::maybe_grow(1024 * 64, 1024 * 1024, f)
}
#[cfg(not(feature = "stacker"))]
#[inline]
pub(crate) fn recurse<R, F: FnOnce() -> R>(f: F) -> R {
    f()
}

impl<'a, 'b, I, O, E> ParserSealed<'a, I, O, E> for Recursive<Indirect<'a, 'b, I, O, E>>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        recurse(move || {
            M::invoke(
                self.parser()
                    .inner
                    .get()
                    .expect("Recursive parser used before being defined")
                    .as_ref(),
                inp,
            )
        })
    }

    go_extra!(O);
}

impl<'a, 'b, I, O, E> ParserSealed<'a, I, O, E> for Recursive<Direct<'a, 'b, I, O, E>>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        recurse(move || M::invoke(&*self.parser(), inp))
    }

    go_extra!(O);
}

/// Construct a recursive parser (i.e: a parser that may contain itself as part of its pattern).
///
/// The given function must create the parser. The parser must not be used to parse input before this function returns.
///
/// This is a wrapper around [`Recursive::declare`] and [`Recursive::define`].
///
/// The output type of this parser is `O`, the same as the inner parser.
///
/// # Examples
///
/// ```
/// # use chumsky::prelude::*;
/// #[derive(Debug, PartialEq)]
/// enum Tree<'a> {
///     Leaf(&'a str),
///     Branch(Vec<Tree<'a>>),
/// }
///
/// // Parser that recursively parses nested lists
/// let tree = recursive::<_, _, extra::Err<Simple<char>>, _, _>(|tree| tree
///     .separated_by(just(','))
///     .collect::<Vec<_>>()
///     .delimited_by(just('['), just(']'))
///     .map(Tree::Branch)
///     .or(text::ascii::ident().map(Tree::Leaf))
///     .padded());
///
/// assert_eq!(tree.parse("hello").into_result(), Ok(Tree::Leaf("hello")));
/// assert_eq!(tree.parse("[a, b, c]").into_result(), Ok(Tree::Branch(vec![
///     Tree::Leaf("a"),
///     Tree::Leaf("b"),
///     Tree::Leaf("c"),
/// ])));
/// // The parser can deal with arbitrarily complex nested lists
/// assert_eq!(tree.parse("[[a, b], c, [d, [e, f]]]").into_result(), Ok(Tree::Branch(vec![
///     Tree::Branch(vec![
///         Tree::Leaf("a"),
///         Tree::Leaf("b"),
///     ]),
///     Tree::Leaf("c"),
///     Tree::Branch(vec![
///         Tree::Leaf("d"),
///         Tree::Branch(vec![
///             Tree::Leaf("e"),
///             Tree::Leaf("f"),
///         ]),
///     ]),
/// ])));
/// ```
// INFO: Clone bound not actually needed, but good to be safe for future compat
pub fn recursive<'a, 'b, I, O, E, A, F>(f: F) -> Recursive<Indirect<'a, 'b, I, O, E>>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E> + Clone + MaybeSync + 'b,
    F: FnOnce(Recursive<Indirect<'a, 'b, I, O, E>>) -> A,
{
    recursive_fold(|recursive| (f(recursive), ())).0
}

/// Construct two mutually recursive parsers (i.e: two parser that may reference each other).
///
/// The given function must create the parser. The parser must not be used to parse input before this function returns.
///
/// The output type of this parser is `O1`, the same as the inner parser.
///
/// # Examples
///
/// ```
/// # use chumsky::prelude::*;
/// use chumsky::recursive::recursive_2;
/// #[derive(Debug, PartialEq)]
/// enum Tree<'a> {
///     Leaf(&'a str),
///     Branch(Vec<Tree<'a>>),
/// }
///
/// // Parser that recursively parses nested lists with ordinary or square brackets
/// let tree = recursive_2::<_, _, _, extra::Err<Simple<char>>, _, _, _, _>(|bracket, square| {
///   (choice((bracket.clone()
///     .separated_by(just(','))
///      .collect::<Vec<_>>()
///     .delimited_by(just('('), just(')'))
///     .map(Tree::Branch)
///     .or(text::ascii::ident().map(Tree::Leaf))
///     .padded(), square.clone())),
///   choice((square
///     .separated_by(just(','))
///     .collect::<Vec<_>>()
///     .delimited_by(just('['), just(']'))
///     .map(Tree::Branch)
///     .or(text::ascii::ident().map(Tree::Leaf))
///     .padded(), bracket.clone())))
/// });
///
/// assert_eq!(tree.parse("hello").into_result(), Ok(Tree::Leaf("hello")));
/// assert_eq!(tree.parse("(a, b, c)").into_result(), Ok(Tree::Branch(vec![
///     Tree::Leaf("a"),
///     Tree::Leaf("b"),
///     Tree::Leaf("c"),
/// ])));
/// // The parser can deal with arbitrarily complex nested lists
/// assert_eq!(tree.parse("[(a, b), c, [d, (e, f)]]").into_result(), Ok(Tree::Branch(vec![
///     Tree::Branch(vec![
///         Tree::Leaf("a"),
///         Tree::Leaf("b"),
///     ]),
///     Tree::Leaf("c"),
///     Tree::Branch(vec![
///         Tree::Leaf("d"),
///         Tree::Branch(vec![
///             Tree::Leaf("e"),
///             Tree::Leaf("f"),
///         ]),
///     ]),
/// ])));
/// // Both sides of the parser can be used
/// assert_eq!(tree.flip().parse("(a, b, c)").into_result(), Ok(Tree::Branch(vec![
///     Tree::Leaf("a"),
///     Tree::Leaf("b"),
///     Tree::Leaf("c"),
/// ])));
/// ```
///
///
pub fn recursive_2<'a, 'b, I, O1, O2, E, A1, A2, R, F>(
    f: F,
) -> EitherParser<Recursive<Indirect<'a, 'b, I, O1, E>>, Recursive<Indirect<'a, 'b, I, O2, E>>>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A1: Parser<'a, I, O1, E> + Clone + MaybeSync + 'b,
    A2: Parser<'a, I, O2, E> + Clone + MaybeSync + 'b,
    R: Into<EitherParser<A1, A2>>,
    F: FnOnce(Recursive<Indirect<'a, 'b, I, O1, E>>, Recursive<Indirect<'a, 'b, I, O2, E>>) -> R,
{
    recursive_fold(|left| recursive_fold(|right| f(left, right).into().flip()).flip())
}

/// Construct an EitherParser<A1, A2> with A1 recursive and a guarantee that A1 and A2 are dropped together.
/// This function is useful for constructing recursive parser combinators.
///
/// The given function must create the parser. The parser must not be used to parse input before this function returns.
///
/// The output type of this parser is `O1`, the same as the left parser.
///
/// # Examples
///
/// Please see [recursive] and [recursive_2] for how recursive_fold can be used to define new recursive combinators.
pub fn recursive_fold<'a, 'b, I, O1, A1, A2, R, F, E>(
    f: F,
) -> EitherParser<Recursive<Indirect<'a, 'b, I, O1, E>>, A2>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A1: Parser<'a, I, O1, E> + Clone + MaybeSync + 'b,
    R: Into<EitherParser<A1, A2>>,
    F: FnOnce(Recursive<Indirect<'a, 'b, I, O1, E>>) -> R,
{
    let mut left_parser = Recursive::declare();
    let either = f(left_parser.weak()).into();
    left_parser.define(either.0);
    EitherParser(left_parser, either.1)
}

/// A parser that parses using A1 while guaranteeing that A1 and A2 are dropped together.
#[derive(Clone)]
pub struct EitherParser<A1, A2>(A1, A2);

impl<A1, A2> From<(A1, A2)> for EitherParser<A1, A2> {
    fn from(value: (A1, A2)) -> Self {
        EitherParser(value.0, value.1)
    }
}

impl<'a, I, O, E, A1, A2> ParserSealed<'a, I, O, E> for EitherParser<A1, A2>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A1: Parser<'a, I, O, E>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        self.0.go::<M>(inp)
    }

    go_extra!(O);
}

impl<A1, A2> EitherParser<A1, A2> {
    /// Flip the position of A1 and A2
    pub fn flip(self) -> EitherParser<A2, A1> {
        EitherParser(self.1, self.0)
    }

    #[allow(missing_docs)]
    pub fn left(&self) -> &A1 {
        &self.0
    }

    #[allow(missing_docs)]
    pub fn right(&self) -> &A2 {
        &self.1
    }
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;
    use crate::recursive::{recursive_2, RecursiveInner};

    #[test]
    fn no_strong_references_after_drop() {
        fn check_ref_count<T>(recursive_inner: &RecursiveInner<T>, expected: usize) {
            match recursive_inner {
                RecursiveInner::Owned(_) => {
                    panic!("a user must not have access to strong references")
                }
                RecursiveInner::Unowned(weak) => {
                    assert_eq!(weak.strong_count(), expected);
                }
            };
        }

        let mut smuggle_r1 = None;
        let mut smuggle_r2 = None;

        {
            let _ = recursive_2::<&str, (), (), extra::Err<Simple<char>>, _, _, _, _>(|r1, r2| {
                check_ref_count(&r1.inner, 1);
                check_ref_count(&r2.inner, 1);
                smuggle_r1.replace(r1.clone());
                smuggle_r2.replace(r2.clone());
                (r1, r2)
            });
        }

        check_ref_count(&smuggle_r1.unwrap().inner, 0);
        check_ref_count(&smuggle_r2.unwrap().inner, 0);
    }
}
