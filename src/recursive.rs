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

use alloc::rc::{Rc, Weak};

// TODO: Remove when `OnceCell` is stable
struct OnceCell<T>(core::cell::RefCell<Option<T>>);
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

enum RecursiveInner<T> {
    Owned(Rc<T>),
    Unowned(Weak<T>),
}

type OnceParser<'a, I, O, E> = OnceCell<Box<dyn Parser<I, O, Error = E> + 'a>>;

/// A parser that can be defined in terms of itself by separating its [declaration](Recursive::declare) from its
/// [definition](Recursive::define).
///
/// Prefer to use [`recursive()`], which exists as a convenient wrapper around both operations, if possible.
#[must_use]
pub struct Recursive<'a, I, O, E: Error<I>>(RecursiveInner<OnceParser<'a, I, O, E>>);

impl<'a, I: Clone, O, E: Error<I>> Recursive<'a, I, O, E> {
    fn cell(&self) -> Rc<OnceParser<'a, I, O, E>> {
        match &self.0 {
            RecursiveInner::Owned(x) => x.clone(),
            RecursiveInner::Unowned(x) => x
                .upgrade()
                .expect("Recursive parser used before being defined"),
        }
    }

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
    /// let mut chain = Recursive::<_, _, Simple<char>>::declare();
    ///
    /// // Define the parser in terms of itself.
    /// // In this case, the parser parses a right-recursive list of '+' into a singly linked list
    /// chain.define(just('+')
    ///     .then(chain.clone())
    ///     .map(|(c, chain)| Chain::Link(c, Box::new(chain)))
    ///     .or_not()
    ///     .map(|chain| chain.unwrap_or(Chain::End)));
    ///
    /// assert_eq!(chain.parse(""), Ok(Chain::End));
    /// assert_eq!(
    ///     chain.parse("++"),
    ///     Ok(Chain::Link('+', Box::new(Chain::Link('+', Box::new(Chain::End))))),
    /// );
    /// ```
    pub fn declare() -> Self {
        Recursive(RecursiveInner::Owned(Rc::new(OnceCell::new())))
    }

    /// Defines the parser after declaring it, allowing it to be used for parsing.
    pub fn define<P: Parser<I, O, Error = E> + 'a>(&mut self, parser: P) {
        self.cell()
            .set(Box::new(parser))
            .unwrap_or_else(|_| panic!("Parser defined more than once"));
    }
}

impl<'a, I: Clone, O, E: Error<I>> Clone for Recursive<'a, I, O, E> {
    fn clone(&self) -> Self {
        Self(match &self.0 {
            RecursiveInner::Owned(x) => RecursiveInner::Owned(x.clone()),
            RecursiveInner::Unowned(x) => RecursiveInner::Unowned(x.clone()),
        })
    }
}

impl<'a, I: Clone, O, E: Error<I>> Parser<I, O> for Recursive<'a, I, O, E> {
    type Error = E;

    fn parse_inner<D: Debugger>(
        &self,
        debugger: &mut D,
        stream: &mut StreamOf<I, Self::Error>,
    ) -> PResult<I, O, Self::Error> {
        #[cfg(feature = "stacker")]
        #[inline(always)]
        fn recurse<R, F: FnOnce() -> R>(f: F) -> R {
            stacker::maybe_grow(1024 * 1024, 1024 * 1024, f)
        }
        #[cfg(not(feature = "stacker"))]
        #[inline(always)]
        fn recurse<R, F: FnOnce() -> R>(f: F) -> R {
            f()
        }

        recurse(|| {
            #[allow(deprecated)]
            debugger.invoke(
                self.cell()
                    .get()
                    .expect("Recursive parser used before being defined")
                    .as_ref(),
                stream,
            )
        })
    }

    fn parse_inner_verbose(&self, d: &mut Verbose, s: &mut StreamOf<I, E>) -> PResult<I, O, E> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
    fn parse_inner_silent(&self, d: &mut Silent, s: &mut StreamOf<I, E>) -> PResult<I, O, E> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
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
/// enum Tree {
///     Leaf(String),
///     Branch(Vec<Tree>),
/// }
///
/// // Parser that recursively parses nested lists
/// let tree = recursive::<_, _, _, _, Simple<char>>(|tree| tree
///     .separated_by(just(','))
///     .delimited_by(just('['), just(']'))
///     .map(Tree::Branch)
///     .or(text::ident().map(Tree::Leaf))
///     .padded());
///
/// assert_eq!(tree.parse("hello"), Ok(Tree::Leaf("hello".to_string())));
/// assert_eq!(tree.parse("[a, b, c]"), Ok(Tree::Branch(vec![
///     Tree::Leaf("a".to_string()),
///     Tree::Leaf("b".to_string()),
///     Tree::Leaf("c".to_string()),
/// ])));
/// // The parser can deal with arbitrarily complex nested lists
/// assert_eq!(tree.parse("[[a, b], c, [d, [e, f]]]"), Ok(Tree::Branch(vec![
///     Tree::Branch(vec![
///         Tree::Leaf("a".to_string()),
///         Tree::Leaf("b".to_string()),
///     ]),
///     Tree::Leaf("c".to_string()),
///     Tree::Branch(vec![
///         Tree::Leaf("d".to_string()),
///         Tree::Branch(vec![
///             Tree::Leaf("e".to_string()),
///             Tree::Leaf("f".to_string()),
///         ]),
///     ]),
/// ])));
/// ```
pub fn recursive<
    'a,
    I: Clone,
    O,
    P: Parser<I, O, Error = E> + 'a,
    F: FnOnce(Recursive<'a, I, O, E>) -> P,
    E: Error<I>,
>(
    f: F,
) -> Recursive<'a, I, O, E> {
    let mut parser = Recursive::declare();
    parser.define(f(Recursive(match &parser.0 {
        RecursiveInner::Owned(x) => RecursiveInner::Unowned(Rc::downgrade(x)),
        RecursiveInner::Unowned(_) => unreachable!(),
    })));
    parser
}
