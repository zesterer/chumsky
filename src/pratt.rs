//! Utilities for parsing expressions using
//! [Pratt parsing](https://en.wikipedia.org/wiki/Operator-precedence_parser#Pratt_parsing).
//!
//! *“Who am I? What is my purpose in life? Does it really, cosmically speaking, matter if I don’t get up and go to work?”*
//!
//! Pratt parsing is a powerful technique for defining and parsing operators of varying arity, precedence, and
//! associativity. Unlike [precedence climbing](https://en.wikipedia.org/wiki/Operator-precedence_parser), which
//! defines operator precedence by structurally composing parsers of decreasing precedence, Pratt parsing defines
//! precedence through a numerical
//! ['binding power'](https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html#From-Precedence-to-Binding-Power)
//! that determines how strongly operators should bind to the operands around them.
//!
//! Pratt parsers are defined with the [`Parser::pratt`] method.
//!
//! When writing pratt parsers, it is necessary to first define an 'atomic' operand used by the parser for building up
//! expressions. In most languages, atoms are simple, self-delimiting patterns such as numeric and string literals,
//! identifiers, or parenthesised expressions. Once an atom has been defined, operators can also be defined that
//! operate upon said atoms.
//!
//! # Fold functions
//!
//! Because operators bind atoms together, pratt parsers require you to specify, for each operator, a function that
//! combines its operands together into a syntax tree. These functions are given as the last arguments of [`infix`],
//! [`prefix`], and [`postfix`].
//!
//! # Examples
//!
//! ```
//! use chumsky::prelude::*;
//! use chumsky::pratt::*;
//! use chumsky::extra;
//!
//! enum Expr {
//!     Add(Box<Self>, Box<Self>),
//!     Sub(Box<Self>, Box<Self>),
//!     Pow(Box<Self>, Box<Self>),
//!     Neg(Box<Self>),
//!     Factorial(Box<Self>),
//!     Deref(Box<Self>),
//!     Literal(i32),
//! }
//!
//! impl std::fmt::Display for Expr {
//!     fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
//!         match self {
//!             Self::Literal(literal) => write!(f, "{literal}"),
//!             Self::Factorial(left) => write!(f, "({left}!)"),
//!             Self::Deref(left) => write!(f, "(*{left})"),
//!             Self::Neg(right) => write!(f, "(-{right})"),
//!             Self::Add(left, right) => write!(f, "({left} + {right})"),
//!             Self::Sub(left, right) => write!(f, "({left} - {right})"),
//!             Self::Pow(left, right) => write!(f, "({left} ^ {right})"),
//!         }
//!     }
//! }
//!
//! let atom = text::int::<_, extra::Err<Simple<char>>>(10)
//!     .from_str()
//!     .unwrapped()
//!     .map(Expr::Literal)
//!     .padded();
//!
//! let op = |c| just(c).padded();
//!
//! let expr = atom.pratt((
//!     // We want factorial to happen before any negation, so we
//!     // need its precedence to be higher than `Expr::Neg`.
//!     postfix(4, op('!'), |lhs, _, _| Expr::Factorial(Box::new(lhs))),
//!     // Just like in math, we want that if we write -x^2, our parser
//!     // parses that as -(x^2), so we need it to have exponents bind
//!     // tighter than our prefix operators.
//!     infix(right(3), op('^'), |l, _, r, _| Expr::Pow(Box::new(l), Box::new(r))),
//!     // Notice the conflict with our `Expr::Sub`. This will still
//!     // parse correctly. We want negation to happen before `+` and
//!     // `-`, so we set its precedence higher.
//!     prefix(2, op('-'), |_, rhs, _| Expr::Neg(Box::new(rhs))),
//!     prefix(2, op('*'), |_, rhs, _| Expr::Deref(Box::new(rhs))),
//!     // Our `-` and `+` bind the weakest, meaning that even if they
//!     // occur first in an expression, they will be the last executed.
//!     infix(left(1), op('+'), |l, _, r, _| Expr::Add(Box::new(l), Box::new(r))),
//!     infix(left(1), op('-'), |l, _, r, _| Expr::Sub(Box::new(l), Box::new(r))),
//! ))
//!     .map(|x| x.to_string());
//!
//! assert_eq!(
//!     expr.parse("*1 + -2! - -3^2").into_result(),
//!     Ok("(((*1) + (-(2!))) - (-(3 ^ 2)))".to_string()),
//! );
//! ```

use super::*;

/// The result of calling [`Operator::do_parse_prefix`], [`Operator::do_parse_postfix`] or [`Operator::do_parse_infix`]
pub enum OperatorResult<T, E> {
    /// Input was parsed
    Ok(T),
    /// Input could not be parsed, not fatal
    NoMatch(E),
    /// Input could not be parsed, fatal error
    Err(E),
}

macro_rules! op_check_and_emit {
    () => {
        #[inline(always)]
        fn do_parse_prefix_check<'parse>(
            &self,
            inp: &mut InputRef<'src, 'parse, I, E>,
            pre_expr: &input::Checkpoint<
                'src,
                'parse,
                I,
                <E::State as Inspector<'src, I>>::Checkpoint,
            >,
            f: &dyn Fn(&mut InputRef<'src, 'parse, I, E>, i32) -> PResult<Check, O>,
        ) -> OperatorResult<<Check as Mode>::Output<O>, ()> {
            self.do_parse_prefix::<Check>(inp, pre_expr, &f)
        }
        #[inline(always)]
        fn do_parse_prefix_emit<'parse>(
            &self,
            inp: &mut InputRef<'src, 'parse, I, E>,
            pre_expr: &input::Checkpoint<
                'src,
                'parse,
                I,
                <E::State as Inspector<'src, I>>::Checkpoint,
            >,
            f: &dyn Fn(&mut InputRef<'src, 'parse, I, E>, i32) -> PResult<Emit, O>,
        ) -> OperatorResult<<Emit as Mode>::Output<O>, ()> {
            self.do_parse_prefix::<Emit>(inp, pre_expr, &f)
        }
        #[inline(always)]
        fn do_parse_postfix_check<'parse>(
            &self,
            inp: &mut InputRef<'src, 'parse, I, E>,
            pre_expr: &input::Cursor<'src, 'parse, I>,
            pre_op: &input::Checkpoint<
                'src,
                'parse,
                I,
                <E::State as Inspector<'src, I>>::Checkpoint,
            >,
            lhs: (),
            min_power: i32,
        ) -> OperatorResult<(), ()> {
            self.do_parse_postfix::<Check>(inp, pre_expr, pre_op, lhs, min_power)
        }
        #[inline(always)]
        fn do_parse_postfix_emit<'parse>(
            &self,
            inp: &mut InputRef<'src, 'parse, I, E>,
            pre_expr: &input::Cursor<'src, 'parse, I>,
            pre_op: &input::Checkpoint<
                'src,
                'parse,
                I,
                <E::State as Inspector<'src, I>>::Checkpoint,
            >,
            lhs: O,
            min_power: i32,
        ) -> OperatorResult<O, O> {
            self.do_parse_postfix::<Emit>(inp, pre_expr, pre_op, lhs, min_power)
        }
        #[inline(always)]
        fn do_parse_infix_check<'parse>(
            &self,
            inp: &mut InputRef<'src, 'parse, I, E>,
            pre_expr: &input::Cursor<'src, 'parse, I>,
            pre_op: &input::Checkpoint<
                'src,
                'parse,
                I,
                <E::State as Inspector<'src, I>>::Checkpoint,
            >,
            lhs: (),
            min_power: i32,
            f: &dyn Fn(&mut InputRef<'src, 'parse, I, E>, i32) -> PResult<Check, O>,
        ) -> OperatorResult<(), ()> {
            self.do_parse_infix::<Check>(inp, pre_expr, pre_op, lhs, min_power, &f)
        }
        #[inline(always)]
        fn do_parse_infix_emit<'parse>(
            &self,
            inp: &mut InputRef<'src, 'parse, I, E>,
            pre_expr: &input::Cursor<'src, 'parse, I>,
            pre_op: &input::Checkpoint<
                'src,
                'parse,
                I,
                <E::State as Inspector<'src, I>>::Checkpoint,
            >,
            lhs: O,
            min_power: i32,
            f: &dyn Fn(&mut InputRef<'src, 'parse, I, E>, i32) -> PResult<Emit, O>,
        ) -> OperatorResult<O, O> {
            self.do_parse_infix::<Emit>(inp, pre_expr, pre_op, lhs, min_power, &f)
        }
    };
}

/// A type implemented by pratt parser operators.
pub trait Operator<'src, I, O, E>
where
    I: Input<'src>,
    E: ParserExtra<'src, I>,
{
    /// Box this operator, allowing it to be used via dynamic dispatch.
    fn boxed<'a>(self) -> Boxed<'src, 'a, I, O, E>
    where
        Self: Sized + 'a,
    {
        Boxed(Rc::new(self))
    }

    #[doc(hidden)]
    #[inline(always)]
    fn do_parse_prefix<'parse, M: Mode>(
        &self,
        _inp: &mut InputRef<'src, 'parse, I, E>,
        _pre_expr: &input::Checkpoint<
            'src,
            'parse,
            I,
            <E::State as Inspector<'src, I>>::Checkpoint,
        >,
        _f: &impl Fn(&mut InputRef<'src, 'parse, I, E>, i32) -> PResult<M, O>,
    ) -> OperatorResult<M::Output<O>, ()>
    where
        Self: Sized,
    {
        OperatorResult::NoMatch(())
    }

    #[doc(hidden)]
    #[inline(always)]
    fn do_parse_postfix<'parse, M: Mode>(
        &self,
        _inp: &mut InputRef<'src, 'parse, I, E>,
        _pre_expr: &input::Cursor<'src, 'parse, I>,
        _pre_op: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        lhs: M::Output<O>,
        _min_power: i32,
    ) -> OperatorResult<M::Output<O>, M::Output<O>>
    where
        Self: Sized,
    {
        OperatorResult::NoMatch(lhs)
    }

    #[doc(hidden)]
    #[inline(always)]
    fn do_parse_infix<'parse, M: Mode>(
        &self,
        _inp: &mut InputRef<'src, 'parse, I, E>,
        _pre_expr: &input::Cursor<'src, 'parse, I>,
        _pre_op: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        lhs: M::Output<O>,
        _min_power: i32,
        _f: &impl Fn(&mut InputRef<'src, 'parse, I, E>, i32) -> PResult<M, O>,
    ) -> OperatorResult<M::Output<O>, M::Output<O>>
    where
        Self: Sized,
    {
        OperatorResult::NoMatch(lhs)
    }

    #[doc(hidden)]
    fn do_parse_prefix_check<'parse>(
        &self,
        inp: &mut InputRef<'src, 'parse, I, E>,
        pre_expr: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        f: &dyn Fn(&mut InputRef<'src, 'parse, I, E>, i32) -> PResult<Check, O>,
    ) -> OperatorResult<<Check as Mode>::Output<O>, ()>;
    #[doc(hidden)]
    fn do_parse_prefix_emit<'parse>(
        &self,
        inp: &mut InputRef<'src, 'parse, I, E>,
        pre_expr: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        f: &dyn Fn(&mut InputRef<'src, 'parse, I, E>, i32) -> PResult<Emit, O>,
    ) -> OperatorResult<<Emit as Mode>::Output<O>, ()>;
    #[doc(hidden)]
    fn do_parse_postfix_check<'parse>(
        &self,
        inp: &mut InputRef<'src, 'parse, I, E>,
        pre_expr: &input::Cursor<'src, 'parse, I>,
        pre_op: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        lhs: (),
        min_power: i32,
    ) -> OperatorResult<(), ()>;
    #[doc(hidden)]
    fn do_parse_postfix_emit<'parse>(
        &self,
        inp: &mut InputRef<'src, 'parse, I, E>,
        pre_expr: &input::Cursor<'src, 'parse, I>,
        pre_op: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        lhs: O,
        min_power: i32,
    ) -> OperatorResult<O, O>;
    #[doc(hidden)]
    fn do_parse_infix_check<'parse>(
        &self,
        inp: &mut InputRef<'src, 'parse, I, E>,
        pre_expr: &input::Cursor<'src, 'parse, I>,
        pre_op: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        lhs: (),
        min_power: i32,
        f: &dyn Fn(&mut InputRef<'src, 'parse, I, E>, i32) -> PResult<Check, O>,
    ) -> OperatorResult<(), ()>;
    #[doc(hidden)]
    fn do_parse_infix_emit<'parse>(
        &self,
        inp: &mut InputRef<'src, 'parse, I, E>,
        pre_expr: &input::Cursor<'src, 'parse, I>,
        pre_op: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        lhs: O,
        min_power: i32,
        f: &dyn Fn(&mut InputRef<'src, 'parse, I, E>, i32) -> PResult<Emit, O>,
    ) -> OperatorResult<O, O>;
}

/// A boxed pratt parser operator. See [`Operator`].
pub struct Boxed<'src, 'a, I, O, E = extra::Default>(Rc<DynOperator<'src, 'a, I, O, E>>);

impl<I, O, E> Clone for Boxed<'_, '_, I, O, E> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<'src, I, O, E> Operator<'src, I, O, E> for Boxed<'src, '_, I, O, E>
where
    I: Input<'src>,
    E: ParserExtra<'src, I>,
{
    #[inline(always)]
    fn do_parse_prefix<'parse, M: Mode>(
        &self,
        inp: &mut InputRef<'src, 'parse, I, E>,
        pre_expr: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        f: &impl Fn(&mut InputRef<'src, 'parse, I, E>, i32) -> PResult<M, O>,
    ) -> OperatorResult<M::Output<O>, ()>
    where
        Self: Sized,
    {
        M::invoke_pratt_op_prefix(self, inp, pre_expr, f)
    }

    #[inline(always)]
    fn do_parse_postfix<'parse, M: Mode>(
        &self,
        inp: &mut InputRef<'src, 'parse, I, E>,
        pre_expr: &input::Cursor<'src, 'parse, I>,
        pre_op: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        lhs: M::Output<O>,
        min_power: i32,
    ) -> OperatorResult<M::Output<O>, M::Output<O>>
    where
        Self: Sized,
    {
        M::invoke_pratt_op_postfix(self, inp, pre_expr, pre_op, lhs, min_power)
    }

    #[inline(always)]
    fn do_parse_infix<'parse, M: Mode>(
        &self,
        inp: &mut InputRef<'src, 'parse, I, E>,
        pre_expr: &input::Cursor<'src, 'parse, I>,
        pre_op: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        lhs: M::Output<O>,
        min_power: i32,
        f: &impl Fn(&mut InputRef<'src, 'parse, I, E>, i32) -> PResult<M, O>,
    ) -> OperatorResult<M::Output<O>, M::Output<O>>
    where
        Self: Sized,
    {
        M::invoke_pratt_op_infix(self, inp, pre_expr, pre_op, lhs, min_power, f)
    }

    #[inline(always)]
    fn do_parse_prefix_check<'parse>(
        &self,
        inp: &mut InputRef<'src, 'parse, I, E>,
        pre_expr: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        f: &dyn Fn(&mut InputRef<'src, 'parse, I, E>, i32) -> PResult<Check, O>,
    ) -> OperatorResult<<Check as Mode>::Output<O>, ()> {
        self.0.do_parse_prefix_check(inp, pre_expr, f)
    }
    #[inline(always)]
    fn do_parse_prefix_emit<'parse>(
        &self,
        inp: &mut InputRef<'src, 'parse, I, E>,
        pre_expr: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        f: &dyn Fn(&mut InputRef<'src, 'parse, I, E>, i32) -> PResult<Emit, O>,
    ) -> OperatorResult<<Emit as Mode>::Output<O>, ()> {
        self.0.do_parse_prefix_emit(inp, pre_expr, f)
    }
    #[inline(always)]
    fn do_parse_postfix_check<'parse>(
        &self,
        inp: &mut InputRef<'src, 'parse, I, E>,
        pre_expr: &input::Cursor<'src, 'parse, I>,
        pre_op: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        lhs: (),
        min_power: i32,
    ) -> OperatorResult<(), ()> {
        self.0
            .do_parse_postfix_check(inp, pre_expr, pre_op, lhs, min_power)
    }
    #[inline(always)]
    fn do_parse_postfix_emit<'parse>(
        &self,
        inp: &mut InputRef<'src, 'parse, I, E>,
        pre_expr: &input::Cursor<'src, 'parse, I>,
        pre_op: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        lhs: O,
        min_power: i32,
    ) -> OperatorResult<O, O> {
        self.0
            .do_parse_postfix_emit(inp, pre_expr, pre_op, lhs, min_power)
    }
    #[inline(always)]
    fn do_parse_infix_check<'parse>(
        &self,
        inp: &mut InputRef<'src, 'parse, I, E>,
        pre_expr: &input::Cursor<'src, 'parse, I>,
        pre_op: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        lhs: (),
        min_power: i32,
        f: &dyn Fn(&mut InputRef<'src, 'parse, I, E>, i32) -> PResult<Check, O>,
    ) -> OperatorResult<(), ()> {
        self.0
            .do_parse_infix_check(inp, pre_expr, pre_op, lhs, min_power, &f)
    }
    #[inline(always)]
    fn do_parse_infix_emit<'parse>(
        &self,
        inp: &mut InputRef<'src, 'parse, I, E>,
        pre_expr: &input::Cursor<'src, 'parse, I>,
        pre_op: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        lhs: O,
        min_power: i32,
        f: &dyn Fn(&mut InputRef<'src, 'parse, I, E>, i32) -> PResult<Emit, O>,
    ) -> OperatorResult<O, O> {
        self.0
            .do_parse_infix_emit(inp, pre_expr, pre_op, lhs, min_power, &f)
    }
}

/// Defines the [associativity](https://en.wikipedia.org/wiki/Associative_property) and precedence of an [`infix`]
/// operator (see [`left`], [`right`] and [`none`]).
///
/// Higher numbers should be used for higher precedence operators.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Associativity {
    /// Specifies that the operator should be left-associative, with the given precedence (see [`left`]).
    Left(u16),
    /// Specifies that the operator should be right-associative, with the given precedence (see [`right`]).
    Right(u16),
    /// Specifies that the operator is non-associative, with the given precedence (see [`none`]).
    None(u16),
}

/// Specifies a left [`Associativity`] with the given precedence.
///
/// Left-associative operators are evaluated from the left-most terms, moving rightward. For example, the expression
/// `a + b + c + d` will be evaluated as `((a + b) + c) + d` because addition is conventionally left-associative.
pub fn left(precedence: u16) -> Associativity {
    Associativity::Left(precedence)
}

/// Specifies a right [`Associativity`] with the given precedence.
///
/// Right-associative operators are evaluated from the right-most terms, moving leftward. For example, the expression
/// `a ^ b ^ c ^ d` will be evaluated as `a ^ (b ^ (c ^ d))` because exponents are conventionally right-associative.
pub fn right(precedence: u16) -> Associativity {
    Associativity::Right(precedence)
}

/// Specifies no [`Associativity`] with the given precedence.
///
/// Non-associative operators can't be chained. For example, the expression
/// `a < b < c` will produce an error, because comparisons are conventionally non-associative.
pub fn none(precedence: u16) -> Associativity {
    Associativity::None(precedence)
}

impl Associativity {
    fn left_power(&self) -> i32 {
        match self {
            Self::Left(x) => *x as i32 * 2,
            Self::Right(x) => *x as i32 * 2 + 1,
            Self::None(x) => *x as i32 * 2,
        }
    }

    fn right_power(&self) -> i32 {
        match self {
            Self::Left(x) => *x as i32 * 2 + 1,
            Self::Right(x) => *x as i32 * 2,
            Self::None(x) => *x as i32 * 2,
        }
    }
}

/// See [`infix`].
pub struct Infix<'src, A, F, Atom, Op, I, E> {
    op_parser: A,
    fold: F,
    associativity: Associativity,
    #[allow(dead_code)]
    phantom: EmptyPhantom<&'src (Atom, Op, I, E)>,
}

impl<A: Copy, F: Copy, Atom, Op, I, E> Copy for Infix<'_, A, F, Atom, Op, I, E> {}
impl<A: Clone, F: Clone, Atom, Op, I, E> Clone for Infix<'_, A, F, Atom, Op, I, E> {
    fn clone(&self) -> Self {
        Self {
            op_parser: self.op_parser.clone(),
            fold: self.fold.clone(),
            associativity: self.associativity,
            phantom: EmptyPhantom::new(),
        }
    }
}

/// Specify a binary infix operator for a pratt parser with the given associativity, precedence, and
/// [fold function](crate::pratt#fold-functions).
///
/// Operators like addition, subtraction, multiplication, division, remainder, exponentiation, etc. are infix binary
/// operators in most languages.
///
/// See [`left`] and [`right`] for information about associativity.
///
/// The fold function (the last argument) tells the parser how to combine the operator and operands into a new
/// expression. It must have the following signature:
///
/// ```ignore
/// impl Fn(Atom, Op, Atom, &mut MapExtra<'src, '_, I, E>) -> O
/// ```
pub const fn infix<'src, A, F, Atom, Op, I, E>(
    associativity: Associativity,
    op_parser: A,
    fold: F,
) -> Infix<'src, A, F, Atom, Op, I, E>
where
    F: Fn(Atom, Op, Atom, &mut MapExtra<'src, '_, I, E>) -> Atom,
{
    Infix {
        op_parser,
        fold,
        associativity,
        phantom: EmptyPhantom::new(),
    }
}

impl<'src, I, O, E, A, F, Op> Operator<'src, I, O, E> for Infix<'src, A, F, O, Op, I, E>
where
    I: Input<'src>,
    E: ParserExtra<'src, I>,
    A: Parser<'src, I, Op, E>,
    F: Fn(O, Op, O, &mut MapExtra<'src, '_, I, E>) -> O,
{
    #[inline]
    fn do_parse_infix<'parse, M: Mode>(
        &self,
        inp: &mut InputRef<'src, 'parse, I, E>,
        pre_expr: &input::Cursor<'src, 'parse, I>,
        pre_op: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        lhs: M::Output<O>,
        min_power: i32,
        f: &impl Fn(&mut InputRef<'src, 'parse, I, E>, i32) -> PResult<M, O>,
    ) -> OperatorResult<M::Output<O>, M::Output<O>>
    where
        Self: Sized,
    {
        match self.op_parser.go::<M>(inp) {
            Ok(op) => {
                let binding_power = self.associativity.left_power();

                let power_check = if let Associativity::None(_) = self.associativity {
                    binding_power > min_power
                } else {
                    binding_power >= min_power
                };
                if power_check {
                    match f(inp, self.associativity.right_power()) {
                        Ok(rhs) => OperatorResult::Ok(M::combine(
                            M::combine(lhs, rhs, |lhs, rhs| (lhs, rhs)),
                            op,
                            |(lhs, rhs), op| {
                                (self.fold)(lhs, op, rhs, &mut MapExtra::new(pre_expr, inp))
                            },
                        )),
                        Err(()) => {
                            inp.rewind(pre_op.clone());
                            OperatorResult::NoMatch(lhs)
                        }
                    }
                } else {
                    inp.rewind(pre_op.clone());

                    if binding_power == min_power {
                        // TODO: Add error "Ambigious operator order"
                        OperatorResult::Err(lhs)
                    } else {
                        OperatorResult::NoMatch(lhs)
                    }
                }
            }
            Err(()) => {
                inp.rewind(pre_op.clone());
                OperatorResult::NoMatch(lhs)
            }
        }
    }

    op_check_and_emit!();
}

/// See [`prefix`].
pub struct Prefix<'src, A, F, Atom, Op, I, E> {
    op_parser: A,
    fold: F,
    binding_power: i32,
    #[allow(dead_code)]
    phantom: EmptyPhantom<&'src (Atom, Op, I, E)>,
}

impl<A: Copy, F: Copy, Atom, Op, I, E> Copy for Prefix<'_, A, F, Atom, Op, I, E> {}
impl<A: Clone, F: Clone, Atom, Op, I, E> Clone for Prefix<'_, A, F, Atom, Op, I, E> {
    fn clone(&self) -> Self {
        Self {
            op_parser: self.op_parser.clone(),
            fold: self.fold.clone(),
            binding_power: self.binding_power,
            phantom: EmptyPhantom::new(),
        }
    }
}

/// Specify a unary prefix operator for a pratt parser with the given precedence and
/// [fold function](crate::pratt#fold-functions).
///
/// Operators like negation, not, dereferencing, etc. are prefix unary operators in most languages.
///
/// The fold function (the last argument) tells the parser how to combine the operator and operand into a new
/// expression. It must have the following signature:
///
/// ```ignore
/// impl Fn(Op, Atom, &mut MapExtra<'src, '_, I, E>) -> O
/// ```
pub const fn prefix<'src, A, F, Atom, Op, I, E>(
    precedence: u16,
    op_parser: A,
    fold: F,
) -> Prefix<'src, A, F, Atom, Op, I, E>
where
    F: Fn(Op, Atom, &mut MapExtra<'src, '_, I, E>) -> Atom,
{
    Prefix {
        op_parser,
        fold,
        binding_power: precedence as i32 * 2,
        phantom: EmptyPhantom::new(),
    }
}

impl<'src, I, O, E, A, F, Op> Operator<'src, I, O, E> for Prefix<'src, A, F, O, Op, I, E>
where
    I: Input<'src>,
    E: ParserExtra<'src, I>,
    A: Parser<'src, I, Op, E>,
    F: Fn(Op, O, &mut MapExtra<'src, '_, I, E>) -> O,
{
    #[inline]
    fn do_parse_prefix<'parse, M: Mode>(
        &self,
        inp: &mut InputRef<'src, 'parse, I, E>,
        pre_expr: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        f: &impl Fn(&mut InputRef<'src, 'parse, I, E>, i32) -> PResult<M, O>,
    ) -> OperatorResult<M::Output<O>, ()>
    where
        Self: Sized,
    {
        match self.op_parser.go::<M>(inp) {
            Ok(op) => match f(inp, self.binding_power) {
                Ok(rhs) => OperatorResult::Ok(M::combine(op, rhs, |op, rhs| {
                    (self.fold)(op, rhs, &mut MapExtra::new(pre_expr.cursor(), inp))
                })),
                Err(()) => {
                    inp.rewind(pre_expr.clone());
                    OperatorResult::NoMatch(())
                }
            },
            Err(()) => {
                inp.rewind(pre_expr.clone());
                OperatorResult::NoMatch(())
            }
        }
    }

    op_check_and_emit!();
}

/// See [`postfix`].
pub struct Postfix<'src, A, F, Atom, Op, I, E> {
    op_parser: A,
    fold: F,
    binding_power: i32,
    #[allow(dead_code)]
    phantom: EmptyPhantom<&'src (Atom, Op, I, E)>,
}

impl<A: Copy, F: Copy, Atom, Op, I, E> Copy for Postfix<'_, A, F, Atom, Op, I, E> {}
impl<A: Clone, F: Clone, Atom, Op, I, E> Clone for Postfix<'_, A, F, Atom, Op, I, E> {
    fn clone(&self) -> Self {
        Self {
            op_parser: self.op_parser.clone(),
            fold: self.fold.clone(),
            binding_power: self.binding_power,
            phantom: EmptyPhantom::new(),
        }
    }
}

/// Specify a unary postfix operator for a pratt parser with the given precedence and
/// [fold function](crate::pratt#fold-functions).
///
/// Operators like factorial, field access, etc. are postfix unary operators in most languages.
///
/// The fold function (the last argument) tells the parser how to combine the operator and operand into a new
/// expression. It must have the following signature:
///
/// ```ignore
/// impl Fn(Atom, Op, &mut MapExtra<'src, '_, I, E>) -> O
/// ```
pub const fn postfix<'src, A, F, Atom, Op, I, E>(
    precedence: u16,
    op_parser: A,
    fold: F,
) -> Postfix<'src, A, F, Atom, Op, I, E>
where
    F: Fn(Atom, Op, &mut MapExtra<'src, '_, I, E>) -> Atom,
{
    Postfix {
        op_parser,
        fold,
        binding_power: precedence as i32 * 2 + 1,
        phantom: EmptyPhantom::new(),
    }
}

impl<'src, I, O, E, A, F, Op> Operator<'src, I, O, E> for Postfix<'src, A, F, O, Op, I, E>
where
    I: Input<'src>,
    E: ParserExtra<'src, I>,
    A: Parser<'src, I, Op, E>,
    F: Fn(O, Op, &mut MapExtra<'src, '_, I, E>) -> O,
{
    #[inline]
    fn do_parse_postfix<'parse, M: Mode>(
        &self,
        inp: &mut InputRef<'src, 'parse, I, E>,
        pre_expr: &input::Cursor<'src, 'parse, I>,
        pre_op: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        lhs: M::Output<O>,
        min_power: i32,
    ) -> OperatorResult<M::Output<O>, M::Output<O>>
    where
        Self: Sized,
    {
        if self.binding_power >= min_power {
            match self.op_parser.go::<M>(inp) {
                Ok(op) => OperatorResult::Ok(M::combine(lhs, op, |lhs, op| {
                    (self.fold)(lhs, op, &mut MapExtra::new(pre_expr, inp))
                })),
                Err(()) => {
                    inp.rewind(pre_op.clone());
                    OperatorResult::NoMatch(lhs)
                }
            }
        } else {
            OperatorResult::NoMatch(lhs)
        }
    }

    op_check_and_emit!();
}

/// See [`Parser::pratt`].
#[derive(Copy, Clone)]
pub struct Pratt<Atom, Ops> {
    pub(crate) atom: Atom,
    pub(crate) ops: Ops,
}

macro_rules! impl_operator_for_tuple {
    () => {};
    ($head:ident $($X:ident)*) => {
        impl_operator_for_tuple!($($X)*);
        impl_operator_for_tuple!(~ $head $($X)*);
    };
    (~ $($X:ident)+) => {
        #[allow(unused_variables, non_snake_case)]
        impl<'src, I, O, E, $($X),*> Operator<'src, I, O, E> for ($($X,)*)
            where
                I: Input<'src>,
                E: ParserExtra<'src, I>,
                $($X: Operator<'src, I, O, E>),*
        {
            #[inline]
            fn do_parse_prefix<'parse, M: Mode>(
                &self,
                inp: &mut InputRef<'src, 'parse, I, E>,
                pre_expr: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
                f: &impl Fn(&mut InputRef<'src, 'parse, I, E>, i32) -> PResult<M, O>,
            ) -> OperatorResult<M::Output<O>, ()>
            where
                Self: Sized,
            {
                let ($($X,)*) = self;
                $(
                    match $X.do_parse_prefix::<M>(inp, pre_expr, f) {
                        OperatorResult::NoMatch(out) => {},
                        result => return result,
                    }
                )*
                OperatorResult::NoMatch(())
            }

            #[inline]
            fn do_parse_postfix<'parse, M: Mode>(
                &self,
                inp: &mut InputRef<'src, 'parse, I, E>,
                pre_expr: &input::Cursor<'src, 'parse, I>,
                pre_op: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
                mut lhs: M::Output<O>,
                min_power: i32,
            ) -> OperatorResult<M::Output<O>, M::Output<O>>
            where
                Self: Sized,
            {
                let ($($X,)*) = self;
                $(
                    match $X.do_parse_postfix::<M>(inp, pre_expr, pre_op, lhs, min_power) {
                        OperatorResult::NoMatch(out) => lhs = out,
                        result => return result,
                    }
                )*
                OperatorResult::NoMatch(lhs)
            }

            #[inline]
            fn do_parse_infix<'parse, M: Mode>(
                &self,
                inp: &mut InputRef<'src, 'parse, I, E>,
                pre_expr: &input::Cursor<'src, 'parse, I>,
                pre_op: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
                mut lhs: M::Output<O>,
                min_power: i32,
                f: &impl Fn(&mut InputRef<'src, 'parse, I, E>, i32) -> PResult<M, O>,
            ) -> OperatorResult<M::Output<O>, M::Output<O>>
            where
                Self: Sized,
            {
                let ($($X,)*) = self;
                $(
                    match $X.do_parse_infix::<M>(inp, pre_expr, pre_op, lhs, min_power, f) {
                        OperatorResult::NoMatch(out) => lhs = out,
                        result => return result,
                    }
                )*
                OperatorResult::NoMatch(lhs)
            }

            op_check_and_emit!();
        }
    };
}

impl_operator_for_tuple!(A_ B_ C_ D_ E_ F_ G_ H_ I_ J_ K_ L_ M_ N_ O_ P_ Q_ R_ S_ T_ U_ V_ W_ X_ Y_ Z_);

#[allow(unused_variables, non_snake_case)]
impl<'src, I, O, E, Op> Operator<'src, I, O, E> for Vec<Op>
where
    I: Input<'src>,
    E: ParserExtra<'src, I>,
    Op: Operator<'src, I, O, E>,
{
    #[inline]
    fn do_parse_prefix<'parse, M: Mode>(
        &self,
        inp: &mut InputRef<'src, 'parse, I, E>,
        pre_expr: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        f: &impl Fn(&mut InputRef<'src, 'parse, I, E>, i32) -> PResult<M, O>,
    ) -> OperatorResult<M::Output<O>, ()>
    where
        Self: Sized,
    {
        for op in self {
            match op.do_parse_prefix::<M>(inp, pre_expr, f) {
                OperatorResult::NoMatch(()) => {}
                result => return result,
            }
        }
        OperatorResult::NoMatch(())
    }

    #[inline]
    fn do_parse_postfix<'parse, M: Mode>(
        &self,
        inp: &mut InputRef<'src, 'parse, I, E>,
        pre_expr: &input::Cursor<'src, 'parse, I>,
        pre_op: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        mut lhs: M::Output<O>,
        min_power: i32,
    ) -> OperatorResult<M::Output<O>, M::Output<O>>
    where
        Self: Sized,
    {
        for op in self {
            match op.do_parse_postfix::<M>(inp, pre_expr, pre_op, lhs, min_power) {
                OperatorResult::NoMatch(out) => lhs = out,
                result => return result,
            }
        }
        OperatorResult::NoMatch(lhs)
    }

    #[inline]
    fn do_parse_infix<'parse, M: Mode>(
        &self,
        inp: &mut InputRef<'src, 'parse, I, E>,
        pre_expr: &input::Cursor<'src, 'parse, I>,
        pre_op: &input::Checkpoint<'src, 'parse, I, <E::State as Inspector<'src, I>>::Checkpoint>,
        mut lhs: M::Output<O>,
        min_power: i32,
        f: &impl Fn(&mut InputRef<'src, 'parse, I, E>, i32) -> PResult<M, O>,
    ) -> OperatorResult<M::Output<O>, M::Output<O>>
    where
        Self: Sized,
    {
        for op in self {
            match op.do_parse_infix::<M>(inp, pre_expr, pre_op, lhs, min_power, f) {
                OperatorResult::NoMatch(out) => lhs = out,
                result => return result,
            }
        }
        OperatorResult::NoMatch(lhs)
    }

    op_check_and_emit!();
}

#[allow(unused_variables, non_snake_case)]
impl<'src, Atom, Ops> Pratt<Atom, Ops> {
    #[inline]
    fn pratt_go<M: Mode, I, O, E>(
        &self,
        inp: &mut InputRef<'src, '_, I, E>,
        min_power: i32,
    ) -> PResult<M, O>
    where
        I: Input<'src>,
        E: ParserExtra<'src, I>,
        Atom: Parser<'src, I, O, E>,
        Ops: Operator<'src, I, O, E>,
    {
        let pre_expr = inp.save();
        // Prefix unary operators
        let mut lhs = match self
            .ops
            .do_parse_prefix::<M>(inp, &pre_expr, &|inp, min_power| {
                recursive::recurse(|| self.pratt_go::<M, _, _, _>(inp, min_power))
            }) {
            OperatorResult::Ok(out) => out,
            OperatorResult::NoMatch(()) => self.atom.go::<M>(inp)?,
            OperatorResult::Err(()) => return Err(()),
        };

        loop {
            let pre_op = inp.save();

            // Postfix unary operators
            match self
                .ops
                .do_parse_postfix::<M>(inp, pre_expr.cursor(), &pre_op, lhs, min_power)
            {
                OperatorResult::Ok(out) => {
                    lhs = out;
                    continue;
                }
                OperatorResult::NoMatch(out) => lhs = out,
                OperatorResult::Err(out) => {
                    inp.rewind(pre_op);
                    return Err(());
                }
            }

            // Infix binary operators
            match self.ops.do_parse_infix::<M>(
                inp,
                pre_expr.cursor(),
                &pre_op,
                lhs,
                min_power,
                &|inp, min_power| {
                    recursive::recurse(|| self.pratt_go::<M, _, _, _>(inp, min_power))
                },
            ) {
                OperatorResult::Ok(out) => {
                    lhs = out;
                    continue;
                }
                OperatorResult::NoMatch(out) => lhs = out,
                OperatorResult::Err(out) => {
                    inp.rewind(pre_op);
                    return Err(());
                }
            }

            inp.rewind(pre_op);
            break;
        }

        Ok(lhs)
    }
}

#[allow(unused_variables, non_snake_case)]
impl<'src, I, O, E, Atom, Ops> Parser<'src, I, O, E> for Pratt<Atom, Ops>
where
    I: Input<'src>,
    E: ParserExtra<'src, I>,
    Atom: Parser<'src, I, O, E>,
    Ops: Operator<'src, I, O, E>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, O> {
        self.pratt_go::<M, _, _, _>(inp, i32::MIN)
    }

    go_extra!(O);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{extra::Err, prelude::*};

    fn factorial(x: i64) -> i64 {
        if x == 0 {
            1
        } else {
            x * factorial(x - 1)
        }
    }

    fn parser<'src>() -> impl Parser<'src, &'src str, i64> {
        let atom = text::int(10).padded().from_str::<i64>().unwrapped();

        atom.pratt((
            prefix(2, just('-'), |_, x: i64, _| -x),
            postfix(2, just('!'), |x, _, _| factorial(x)),
            infix(left(0), just('+'), |l, _, r, _| l + r),
            infix(left(0), just('-'), |l, _, r, _| l - r),
            infix(left(1), just('*'), |l, _, r, _| l * r),
            infix(left(1), just('/'), |l, _, r, _| l / r),
        ))
    }

    #[test]
    fn precedence() {
        assert_eq!(parser().parse("2 + 3 * 4").into_result(), Ok(14));
        assert_eq!(parser().parse("2 * 3 + 4").into_result(), Ok(10));
    }

    #[test]
    fn unary() {
        assert_eq!(parser().parse("-2").into_result(), Ok(-2));
        assert_eq!(parser().parse("4!").into_result(), Ok(24));
        assert_eq!(parser().parse("2 + 4!").into_result(), Ok(26));
        assert_eq!(parser().parse("-2 + 2").into_result(), Ok(0));
    }

    #[allow(dead_code)]
    fn parser_dynamic<'src>() -> impl Parser<'src, &'src str, i64> {
        let atom = text::int(10).padded().from_str::<i64>().unwrapped();

        atom.pratt(vec![
            prefix(2, just('-'), |_, x: i64, _| -x).boxed(),
            postfix(2, just('!'), |x, _, _| factorial(x)).boxed(),
            infix(left(0), just('+'), |l, _, r, _| l + r).boxed(),
            infix(left(0), just('-'), |l, _, r, _| l - r).boxed(),
            infix(left(1), just('*'), |l, _, r, _| l * r).boxed(),
            infix(left(1), just('/'), |l, _, r, _| l / r).boxed(),
        ])
    }

    enum Expr {
        Literal(i64),
        Not(Box<Expr>),
        Negate(Box<Expr>),
        Confusion(Box<Expr>),
        Factorial(Box<Expr>),
        Value(Box<Expr>),
        Less(Box<Expr>, Box<Expr>),
        Add(Box<Expr>, Box<Expr>),
        Sub(Box<Expr>, Box<Expr>),
        Mul(Box<Expr>, Box<Expr>),
        Div(Box<Expr>, Box<Expr>),
    }

    impl std::fmt::Display for Expr {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Self::Literal(literal) => write!(f, "{literal}"),
                Self::Not(right) => write!(f, "(~{right})"),
                Self::Negate(right) => write!(f, "(-{right})"),
                Self::Confusion(right) => write!(f, "(§{right})"),
                Self::Factorial(right) => write!(f, "({right}!)"),
                Self::Value(right) => write!(f, "({right}$)"),
                Self::Less(left, right) => write!(f, "({left} < {right})"),
                Self::Add(left, right) => write!(f, "({left} + {right})"),
                Self::Sub(left, right) => write!(f, "({left} - {right})"),
                Self::Mul(left, right) => write!(f, "({left} * {right})"),
                Self::Div(left, right) => write!(f, "({left} / {right})"),
            }
        }
    }

    fn u(e: fn(Box<Expr>) -> Expr, r: Expr) -> Expr {
        e(Box::new(r))
    }
    fn i(e: fn(Box<Expr>, Box<Expr>) -> Expr, l: Expr, r: Expr) -> Expr {
        e(Box::new(l), Box::new(r))
    }

    fn expr_parser<'src>() -> impl Parser<'src, &'src str, String, Err<Simple<'src, char>>> {
        let atom = text::int(10).from_str().unwrapped().map(Expr::Literal);

        atom.pratt((
            infix(left(0), just('+'), |l, _, r, _| i(Expr::Add, l, r)),
            infix(left(0), just('-'), |l, _, r, _| i(Expr::Sub, l, r)),
            infix(right(1), just('*'), |l, _, r, _| i(Expr::Mul, l, r)),
            infix(right(1), just('/'), |l, _, r, _| i(Expr::Div, l, r)),
        ))
        .map(|x| x.to_string())
    }

    fn complete_parser<'src>() -> impl Parser<'src, &'src str, String, Err<Simple<'src, char>>> {
        expr_parser().then_ignore(end())
    }

    fn parse(input: &str) -> ParseResult<String, Simple<'_, char>> {
        complete_parser().parse(input)
    }

    fn parse_partial(input: &str) -> ParseResult<String, Simple<'_, char>> {
        expr_parser().lazy().parse(input)
    }

    fn unexpected<'src, C: Into<Option<MaybeRef<'src, char>>>, S: Into<SimpleSpan>>(
        c: C,
        span: S,
    ) -> Simple<'src, char> {
        <Simple<_> as LabelError<&[char], _>>::expected_found::<[DefaultExpected<char>; 0]>(
            [],
            c.into(),
            span.into(),
        )
    }

    #[test]
    fn missing_first_expression() {
        assert_eq!(parse("").into_result(), Err(vec![unexpected(None, 0..0)]))
    }

    #[test]
    fn missing_later_expression() {
        assert_eq!(parse("1+").into_result(), Err(vec![unexpected(None, 2..2)]),);
    }

    #[test]
    fn invalid_first_expression() {
        assert_eq!(
            parse("?").into_result(),
            Err(vec![unexpected(Some('?'.into()), 0..1)]),
        );
    }

    #[test]
    fn invalid_later_expression() {
        assert_eq!(
            parse("1+?").into_result(),
            Err(vec![dbg!(unexpected(Some('?'.into()), 2..3))]),
        );
    }

    #[test]
    fn invalid_operator() {
        assert_eq!(
            parse("1?").into_result(),
            Err(vec![unexpected(Some('?'.into()), 1..2)]),
        );
    }

    #[test]
    fn invalid_operator_incomplete() {
        assert_eq!(parse_partial("1?").into_result(), Ok("1".to_string()),);
    }

    #[test]
    fn complex_nesting() {
        assert_eq!(
            parse_partial("1+2*3/4*5-6*7+8-9+10").into_result(),
            Ok("(((((1 + (2 * (3 / (4 * 5)))) - (6 * 7)) + 8) - 9) + 10)".to_string()),
        );
    }

    #[test]
    fn with_prefix_ops() {
        let atom = text::int::<_, Err<Simple<char>>>(10)
            .from_str()
            .unwrapped()
            .map(Expr::Literal);

        let parser = atom
            .pratt((
                // -- Prefix
                // Because we defined '*' and '/' as right associative operators,
                // in order to get these to function as expected, their strength
                // must be higher
                prefix(2, just('-'), |_, r, _| u(Expr::Negate, r)),
                prefix(2, just('~'), |_, r, _| u(Expr::Not, r)),
                // This is what happens when not
                prefix(1, just('§'), |_, r, _| u(Expr::Confusion, r)),
                // -- Infix
                infix(left(0), just('+'), |l, _, r, _| i(Expr::Add, l, r)),
                infix(left(0), just('-'), |l, _, r, _| i(Expr::Sub, l, r)),
                infix(right(1), just('*'), |l, _, r, _| i(Expr::Mul, l, r)),
                infix(right(1), just('/'), |l, _, r, _| i(Expr::Div, l, r)),
            ))
            .map(|x| x.to_string());

        assert_eq!(
            parser.parse("-1+§~2*3").into_result(),
            Ok("((-1) + (§((~2) * 3)))".to_string()),
        )
    }

    #[test]
    fn with_postfix_ops() {
        let atom = text::int::<_, Err<Simple<char>>>(10)
            .from_str()
            .unwrapped()
            .map(Expr::Literal);

        let parser = atom
            .pratt((
                // -- Postfix
                // Because we defined '*' and '/' as right associative operators,
                // in order to get these to function as expected, their strength
                // must be higher
                postfix(2, just('!'), |l, _, _| u(Expr::Factorial, l)),
                // This is what happens when not
                postfix(0, just('$'), |l, _, _| u(Expr::Value, l)),
                // -- Infix
                infix(left(1), just('+'), |l, _, r, _| i(Expr::Add, l, r)),
                infix(left(1), just('-'), |l, _, r, _| i(Expr::Sub, l, r)),
                infix(right(2), just('*'), |l, _, r, _| i(Expr::Mul, l, r)),
                infix(right(2), just('/'), |l, _, r, _| i(Expr::Div, l, r)),
            ))
            .map(|x| x.to_string());

        assert_eq!(
            parser.parse("1+2!$*3").into_result(),
            Ok("(((1 + (2!))$) * 3)".to_string()),
        )
    }

    #[test]
    fn with_pre_and_postfix_ops() {
        let atom = text::int::<_, Err<Simple<char>>>(10)
            .from_str()
            .unwrapped()
            .map(Expr::Literal);

        let parser = atom
            .pratt((
                // -- Prefix
                prefix(4, just('-'), |_, r, _| u(Expr::Negate, r)),
                prefix(4, just('~'), |_, r, _| u(Expr::Not, r)),
                prefix(1, just('§'), |_, r, _| u(Expr::Confusion, r)),
                // -- Postfix
                postfix(5, just('!'), |l, _, _| u(Expr::Factorial, l)),
                postfix(0, just('$'), |l, _, _| u(Expr::Value, l)),
                // -- Infix
                infix(left(1), just('+'), |l, _, r, _| i(Expr::Add, l, r)),
                infix(left(1), just('-'), |l, _, r, _| i(Expr::Sub, l, r)),
                infix(right(2), just('*'), |l, _, r, _| i(Expr::Mul, l, r)),
                infix(right(2), just('/'), |l, _, r, _| i(Expr::Div, l, r)),
            ))
            .map(|x| x.to_string());
        assert_eq!(
            parser.parse("§1+-~2!$*3").into_result(),
            Ok("(((§(1 + (-(~(2!)))))$) * 3)".to_string()),
        )
    }

    fn non_associative_parser<'src>(
    ) -> impl Parser<'src, &'src str, String, Err<Simple<'src, char>>> {
        let atom = text::int(10).from_str().unwrapped().map(Expr::Literal);

        atom.pratt((
            infix(none(1), just('<'), |l, _, r, _| i(Expr::Less, l, r)),
            infix(left(2), just('+'), |l, _, r, _| i(Expr::Add, l, r)),
            infix(left(2), just('-'), |l, _, r, _| i(Expr::Sub, l, r)),
            infix(right(3), just('*'), |l, _, r, _| i(Expr::Mul, l, r)),
            infix(right(3), just('/'), |l, _, r, _| i(Expr::Div, l, r)),
        ))
        .map(|x| x.to_string())
    }

    #[test]
    fn with_non_associative_infix_ops() {
        assert_eq!(
            non_associative_parser().parse("1+2*3<10/2").into_result(),
            Ok("((1 + (2 * 3)) < (10 / 2))".to_string()),
        )
    }

    #[test]
    fn with_chained_non_associative_infix_ops() {
        assert_eq!(
            non_associative_parser().parse("1<2<3").into_result(),
            Err(vec![dbg!(unexpected(Some('<'.into()), 3..4))])
        );
        assert_eq!(
            non_associative_parser()
                .parse("1+2*3<10/2<42")
                .into_result(),
            Err(vec![dbg!(unexpected(Some('<'.into()), 10..11))])
        )
    }
}
