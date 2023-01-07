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

enum RecursiveInner<T: ?Sized> {
    Owned(Rc<T>),
    Unowned(Weak<T>),
}

type OnceParser<'a, I, O, E, S> = OnceCell<Box<dyn Parser<'a, I, O, E, S> + 'a>>;

/// Type for recursive parsers that are defined through a call to `recursive`, and as such
/// need no internal indirection
pub type Direct<'a, I, O, E, S = ()> = dyn Parser<'a, I, O, E, S> + 'a;

/// Type for recursive parsers that are defined through a call to [`Recursive::declare`], and as
/// such require an additional layer of allocation.
pub struct Indirect<'a, I: ?Sized, O, E, S = ()> {
    inner: OnceCell<Box<dyn Parser<'a, I, O, E, S> + 'a>>,
}

/// A parser that can be defined in terms of itself by separating its [declaration](Recursive::declare) from its
/// [definition](Recursive::define).
///
/// Prefer to use [`recursive()`], which exists as a convenient wrapper around both operations, if possible.
pub struct Recursive<P: ?Sized> {
    inner: RecursiveInner<P>,
}

impl<'a, I: Input + ?Sized, O, E: Error<I>, S> Recursive<Indirect<'a, I, O, E, S>> {
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
        Recursive {
            inner: RecursiveInner::Owned(Rc::new(Indirect {
                inner: OnceCell::new(),
            })),
        }
    }

    /// Defines the parser after declaring it, allowing it to be used for parsing.
    pub fn define<P: Parser<'a, I, O, E, S> + 'a>(&mut self, parser: P) {
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

impl<'a, I, O, E, S> Parser<'a, I, O, E, S> for Recursive<Indirect<'a, I, O, E, S>>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, O, E> {
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

impl<'a, I, O, E, S> Parser<'a, I, O, E, S> for Recursive<Direct<'a, I, O, E, S>>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, O, E> {
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
pub fn recursive<'a, I, O, E, S, A, F>(f: F) -> Recursive<Direct<'a, I, O, E, S>>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    A: Parser<'a, I, O, E, S> + 'a,
    F: FnOnce(Recursive<Direct<'a, I, O, E, S>>) -> A,
{
    let rc = Rc::new_cyclic(|rc| {
        let rc: Weak<dyn Parser<'a, I, O, E, S>> = rc.clone() as _;
        let parser = Recursive {
            inner: RecursiveInner::Unowned(rc.clone()),
        };

        f(parser)
    });

    Recursive {
        inner: RecursiveInner::Owned(rc),
    }
}
