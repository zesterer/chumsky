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

struct OnceCell<T>(core::cell::Cell<Option<T>>);
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

// TODO: Ensure that this doesn't produce leaks
enum RecursiveInner<T: ?Sized> {
    Owned(Rc<T>),
    Unowned(rc::Weak<T>),
}

/// Type for recursive parsers that are defined through a call to `recursive`, and as such
/// need no internal indirection
pub type Direct<'src, 'b, I, O, Extra> = DynParser<'src, 'b, I, O, Extra>;

/// Type for recursive parsers that are defined through a call to [`Recursive::declare`], and as
/// such require an additional layer of allocation.
pub struct Indirect<'src, 'b, I: Input<'src>, O, Extra: ParserExtra<'src, I>> {
    inner: OnceCell<Box<DynParser<'src, 'b, I, O, Extra>>>,
}

/// A parser that can be defined in terms of itself by separating its [declaration](Recursive::declare) from its
/// [definition](Recursive::define).
///
/// Prefer to use [`recursive()`], which exists as a convenient wrapper around both operations, if possible.
pub struct Recursive<P: ?Sized> {
    inner: RecursiveInner<P>,
}

impl<'src, 'b, I: Input<'src>, O, E: ParserExtra<'src, I>> Recursive<Indirect<'src, 'b, I, O, E>> {
    fn declare() -> Self {
        Recursive {
            inner: RecursiveInner::Owned(Rc::new(Indirect {
                inner: OnceCell::new(),
            })),
        }
    }

    // INFO: Clone bound not actually needed, but good to be safe for future compat
    #[track_caller]
    fn define<P: Parser<'src, I, O, E> + Clone + 'b>(&mut self, parser: P) {
        let location = *Location::caller();
        self.parser()
            .inner
            .set(Box::new(parser))
            .unwrap_or_else(|_| {
                panic!("recursive parsers can only be defined once, trying to redefine it at {location}")
            });
    }

    fn weak(&self) -> Self {
        Self {
            inner: match &self.inner {
                RecursiveInner::Owned(x) => RecursiveInner::Unowned(Rc::downgrade(x)),
                RecursiveInner::Unowned(x) => RecursiveInner::Unowned(x.clone()),
            },
        }
    }
}

impl<P: ?Sized> Recursive<P> {
    #[inline]
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

impl<'src, I, O, E> Parser<'src, I, O, E> for Recursive<Indirect<'src, '_, I, O, E>>
where
    I: Input<'src>,
    E: ParserExtra<'src, I>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, O> {
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

impl<'src, I, O, E> Parser<'src, I, O, E> for Recursive<Direct<'src, '_, I, O, E>>
where
    I: Input<'src>,
    E: ParserExtra<'src, I>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, O> {
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
/// enum Tree<'src> {
///     Leaf(&'src str),
///     Branch(Vec<Tree<'src>>),
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
pub fn recursive<'src, 'b, I, O, E, A, F>(f: F) -> Recursive<Direct<'src, 'b, I, O, E>>
where
    I: Input<'src>,
    E: ParserExtra<'src, I>,
    A: Parser<'src, I, O, E> + Clone + 'b,
    F: FnOnce(Recursive<Direct<'src, 'b, I, O, E>>) -> A,
{
    let rc = Rc::new_cyclic(|rc| {
        let rc: rc::Weak<DynParser<'src, 'b, I, O, E>> = rc.clone() as _;
        let parser = Recursive {
            inner: RecursiveInner::Unowned(rc.clone()),
        };

        f(parser)
    });

    Recursive {
        inner: RecursiveInner::Owned(rc),
    }
}

/// A parser that can be defined in terms of N mutually recursive parsers.
///
/// This is a version of [`Recursive`], which defines a parser in terms of itself.
#[derive(Clone)]
pub struct RecursiveN<P, D> {
    parser: P,
    #[allow(dead_code)]
    dependencies: D,
}

impl<'src, I, O, E, P, D> Parser<'src, I, O, E> for RecursiveN<P, D>
where
    I: Input<'src>,
    E: ParserExtra<'src, I>,
    P: Parser<'src, I, O, E>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, O> {
        self.parser.go::<M>(inp)
    }

    go_extra!(O);
}

/// A trait for types which can be passed into the [`recursive_n`] function.
pub trait RecursiveArgs<'src, 'b, I, O, E, P>: Sized {
    /// The type for the definitions, returned by the parameter to the [`build`](RecursiveArgs::build)
    type Definitions;
    /// The return type of the parsers made by `Self`
    type Return;

    /// A helper type for the macro :D Don't worry.
    type Aux;

    /// Define the recursive parsers, returning a tuple of the primary parser, and it's dependencies.
    fn build<F: FnOnce(Self) -> Self::Definitions>(f: F) -> Self::Return
    where
        I: Input<'src>,
        E: ParserExtra<'src, I>;
}

/// Construct a recursive parser (i.e: a parser that may contain itself as part of its pattern).
///
/// The given function must return definitions for the (currently up to 8) mutually recursive parsers.
/// None of the parsers may be be used to parse within the function.
///
/// The output type of this parser is `O`, the same as the leftmost parser defined by the argument `f`.
///
/// # Note
///
/// For defining multiple mutually recursive parsers, The order of the arguments in must match the order of
/// the definitions out.
///
/// # Examples
///
/// [`recursive_n`] is able to be used when attempting to define a single parser which is dependant on itself.
/// Take for example a tree-structure where each node can either be a letter, or a list of comma separated
/// nodes.
///
/// ```
/// # use chumsky::prelude::*;
/// #[derive(Debug, PartialEq)]
/// enum Tree<'src> {
///     Leaf(&'src str),
///     Branch(Vec<Tree<'src>>),
/// }
///
/// // Parser that recursively parses nested lists
/// let tree = recursive_n::<_, _, extra::Err<Simple<char>>, _, _, _>(|tree: Recursive<_>| tree
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
///
/// # Multiple Recursive Parsers Example
///
/// Unlike the above tree, there are situation when you have multiple parsers which depend on one another.
/// For example, the relationship between statements and expressions in Rust is mutually recursive. A statement,
/// such as an expression statement can contain an expression, and an expression, like a block expression, can
/// contain statements.
///
/// Both of these can also infinitely nest in one another. When trying to model this in chumsky, you can run
/// into an issue because in order to construct a parser for a statement, we must be able to define a parser
/// for an expression and vice-versa. However, this can also be solved with [`recursive_n`].
///
/// Let's take an expression, which can either be an expression in `(` `)`, or a block of statements. A
/// statement can either be an expression followed by a `;`, or a statement wrapped in `[` `]`.
///
/// ```
/// # use chumsky::prelude::*;
/// # #[derive(Debug, PartialEq)]
/// enum Expr {
///     Grouped(Box<Expr>),
///     Block(Vec<Stmt>),
/// }
///
/// # #[derive(Debug, PartialEq)]
/// enum Stmt {
///     Grouped(Box<Stmt>),
///     Expr(Expr),
/// }
///
/// let (stmt, _) = recursive_n::<_, _, extra::Err<Simple<char>>, _, _, _>(|(stmt, expr)| {
///     let expr = choice((
///         stmt.clone()
///             .repeated()
///             .collect()
///             .delimited_by(just('{'), just('}'))
///             .map(Expr::Block),
///         expr.clone()
///             .delimited_by(just('('), just(')'))
///             .map(|expr| Expr::Grouped(Box::new(expr))),
///     ));
///
///     let stmt = choice((
///         expr.clone().then_ignore(just(';')).map(Stmt::Expr),
///         stmt.delimited_by(just('['), just(']'))
///             .map(|stmt| Stmt::Grouped(Box::new(stmt))),
///     ));
///
///     (stmt, expr)
/// });
///
/// assert_eq!(
///     stmt.parse("[{};]").into_result(),
///     Ok(Stmt::Grouped(Box::new(
///         Stmt::Expr(Expr::Block(vec![]),)
///     )))
/// );
///
/// assert_eq!(
///     stmt.parse("{({{};{};});};").into_result(),
///     Ok(Stmt::Expr(Expr::Block(vec![Stmt::Expr(
///         Expr::Grouped(Box::new(Expr::Block(vec![
///             Stmt::Expr(Expr::Block(vec![])),
///             Stmt::Expr(Expr::Block(vec![])),
///         ])))
///     )]),))
/// );
/// ```
pub fn recursive_n<'src, 'b, I, O, E, F, Args, P>(f: F) -> Args::Return
where
    I: Input<'src>,
    E: ParserExtra<'src, I>,
    Args: RecursiveArgs<'src, 'b, I, O, E, P>,
    F: FnOnce(Args) -> Args::Definitions,
{
    Args::build(f)
}

macro_rules! impl_recursive_args_for_tuple {
    () => {};
    ($P1:ident $D1:ident $($X:ident)*) => {
        impl_recursive_args_for_tuple!($($X)*);
        impl_recursive_args_for_tuple!(~ $P1 $D1 $($X)*);
    };
    (~ $Pi:ident $Di:ident $($Pn:ident $Dn:ident)+) => {
        #[allow(unused_variables, non_snake_case)]
        impl<'src, 'b, I, E, $Pi, $Di, $($Pn, $Dn),+> RecursiveArgs<'src, 'b, I, $Di, E, ($Pi, $($Pn),+)>
            for (
                Recursive<Indirect<'src, 'b, I, $Di, E>>,
                $(
                    Recursive<Indirect<'src, 'b, I, $Dn, E>>
                ),+
            )
        where
            I: Input<'src>,
            E: ParserExtra<'src, I>,
            $Pi: Parser<'src, I, $Di, E> + Clone + 'b,
            $($Pn: Parser<'src, I, $Dn, E> + Clone + 'b),+
        {
            type Definitions = ($Pi, $($Pn),+);

            type Aux = (Recursive<Indirect<'src, 'b, I, $Di, E>>, $(Recursive<Indirect<'src, 'b, I, $Dn, E>>),+);

            type Return = (
                RecursiveN<Recursive<Indirect<'src, 'b, I, $Di, E>>, Self::Aux>
                $(
                    ,RecursiveN<Recursive<Indirect<'src, 'b, I, $Dn, E>>, Self::Aux>
                )+
            );

            fn build<F: FnOnce(Self) -> Self::Definitions>(f: F) -> Self::Return {
                  let mut $Pi = Recursive::declare();
                $(let mut $Pn = Recursive::declare();)+

                let ($Di, $($Dn),+) = f(($Pi.weak(), $($Pn.weak()),+));

                  $Pi.define($Di);
                $($Pn.define($Dn);)+

                let deps = ($Pi.clone(), $($Pn.clone()),+);

                (
                    RecursiveN {
                        parser: $Pi.clone(),
                        dependencies: deps.clone(),
                    },
                    $(
                        RecursiveN {
                            parser: $Pn.clone(),
                            dependencies: deps.clone(),
                        }
                    ),+
                )
            }
        }
    };
    (~ $Pi:ident $Di:ident) => {
        #[allow(unused_variables, non_snake_case)]
        impl<'src, 'b, I, E, $Pi, $Di> RecursiveArgs<'src, 'b, I, $Di, E, $Pi>
            for Recursive<Indirect<'src, 'b, I, $Di, E>>
        where
            I: Input<'src>,
            E: ParserExtra<'src, I>,
            $Pi: Parser<'src, I, $Di, E> + Clone + 'b,
        {
            type Definitions = $Pi;

            type Aux = ();

            type Return = RecursiveN<Recursive<Indirect<'src, 'b, I, $Di, E>>, ()>;

            fn build<F: FnOnce(Self) -> Self::Definitions>(f: F) -> Self::Return {
                let mut $Pi = Recursive::declare();

                let $Di = f($Pi.weak());
                $Pi.define($Di);

                RecursiveN {
                    parser: $Pi,
                    dependencies: (),
                }
            }
        }
    };
}

impl_recursive_args_for_tuple!(
    P1 O1
    P2 O2
    P3 O3
    P4 O4
    P5 O5
    P6 O6
    P7 O7
    P8 O8
);
