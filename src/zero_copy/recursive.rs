//! Recursive parsers (parser that include themselves within their patterns).
//!
//! *“It's unpleasantly like being drunk."
//! "What's so unpleasant about being drunk?"
//! "You ask a glass of water.”*
//!
//! The [`recursive()`] function covers most cases, but sometimes it's necessary to manually control the declaration and
//! definition of parsers more corefully, particularly for mutually-recursive parsers. In such cases, the functions on
//! [`Recursive`] allow for this.

use super::*;

#[cfg(feature = "nightly")]
use core::cell::OnceCell;

// TODO: Remove when `OnceCell` is stable
#[cfg(not(feature = "nightly"))]
struct OnceCell<T>(core::cell::RefCell<Option<T>>);
#[cfg(not(feature = "nightly"))]
impl<T> OnceCell<T> {
    pub fn new() -> Self {
        Self(core::cell::RefCell::new(None))
    }
    pub fn set(&self, x: T) -> Result<(), ()> {
        let mut inner = self.0.try_borrow_mut().map_err(|_| ())?;

        if inner.is_none() {
            *inner = Some(x);
            Ok(())
        } else {
            Err(())
        }
    }
    pub fn get(&self) -> Option<core::cell::Ref<T>> {
        Some(core::cell::Ref::map(self.0.borrow(), |x| {
            x.as_ref().unwrap()
        }))
    }
}

enum RecursiveInner<T: ?Sized> {
    Owned(Rc<T>),
    Unowned(Weak<T>),
}

/// Type for recursive parsers that are defined through a call to `recursive`, and as such
/// need no internal indirection
pub type Direct<'a, I, O, Extra> = dyn Parser<'a, I, O, Extra> + 'a;

/// Type for recursive parsers that are defined through a call to [`Recursive::declare`], and as
/// such require an additional layer of allocation.
pub struct Indirect<'a, I: Input<'a>, O, Extra: ParserExtra<'a, I>> {
    inner: OnceCell<Box<dyn Parser<'a, I, O, Extra> + 'a>>,
}

/// A parser that can be defined in terms of itself by separating its [declaration](Recursive::declare) from its
/// [definition](Recursive::define).
///
/// Prefer to use [`recursive()`], which exists as a convenient wrapper around both operations, if possible.
pub struct Recursive<P: ?Sized> {
    inner: RecursiveInner<P>,
}

impl<'a, I: Input<'a>, O, E: ParserExtra<'a, I>> Recursive<Indirect<'a, I, O, E>> {
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
    /// # use chumsky::zero_copy::prelude::*;
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
    /// chain.define(just::<_, _, extra::Err<Simple<&str>>>('+')
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
            inner: RecursiveInner::Owned(Rc::new(Indirect {
                inner: OnceCell::new(),
            })),
        }
    }

    /// Defines the parser after declaring it, allowing it to be used for parsing.
    pub fn define<P: Parser<'a, I, O, E> + Clone + 'a>(&mut self, parser: P) {
        self.parser()
            .inner
            .set(Box::new(parser))
            .unwrap_or_else(|_| panic!("recursive parser already declared"));
    }
}

impl<P: ?Sized> Recursive<P> {
    fn parser(&self) -> Rc<P> {
        match &self.inner {
            RecursiveInner::Owned(x) => x.clone(),
            RecursiveInner::Unowned(x) => x
                .upgrade()
                .expect("Recursive parser used before being defined"),
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

impl<'a, I, O, E> Parser<'a, I, O, E> for Recursive<Indirect<'a, I, O, E>>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        M::invoke(
            self.parser()
                .inner
                .get()
                .expect("Recursive parser used before being defined")
                .as_ref(),
            inp,
        )
    }

    go_extra!(O);
}

impl<'a, I, O, E> Parser<'a, I, O, E> for Recursive<Direct<'a, I, O, E>>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        M::invoke(&*self.parser(), inp)
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
/// # use chumsky::zero_copy::prelude::*;
/// #[derive(Debug, PartialEq)]
/// enum Tree<'a> {
///     Leaf(&'a str),
///     Branch(Vec<Tree<'a>>),
/// }
///
/// // Parser that recursively parses nested lists
/// let tree = recursive::<_, _, extra::Err<Simple<&str>>, _, _>(|tree| tree
///     .separated_by(just(','))
///     .collect::<Vec<_>>()
///     .delimited_by(just('['), just(']'))
///     .map(Tree::Branch)
///     .or(text::ident().map(Tree::Leaf))
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
pub fn recursive<'a, I, O, E, A, F>(f: F) -> Recursive<Direct<'a, I, O, E>>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E> + Clone + 'a,
    F: FnOnce(Recursive<Direct<'a, I, O, E>>) -> A,
{
    let rc = Rc::new_cyclic(|rc| {
        let rc: Weak<dyn Parser<'a, I, O, E>> = rc.clone() as _;
        let parser = Recursive {
            inner: RecursiveInner::Unowned(rc.clone()),
        };

        f(parser)
    });

    Recursive {
        inner: RecursiveInner::Owned(rc),
    }
}
