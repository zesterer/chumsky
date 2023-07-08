//! Pratt parser for efficiently parsing operators while respecting
//! operator precedence.
//!
//! Pratt parsing is an algorithm that allows efficient parsing of
//! expressions using recursion.
//!
//! The [`Parser::pratt`] method creates a [`Pratt`] parser. See the
//! method's documentation for an example of how it can be used.

mod ops;
use ops::Strength;
pub use ops::{InfixOp, PostfixOp, PrefixOp};

use core::{
    cmp::{self, Ordering},
    marker::PhantomData,
};

use crate::{
    extra::ParserExtra,
    input::InputRef,
    prelude::Input,
    private::{Check, Emit, Mode, PResult, ParserSealed},
    Parser,
};

pub(super) use ops::{Infix, InfixPostfix, InfixPrefix, InfixPrefixPostfix, PrattOpOutput};

/// Shorthand for [`InfixOp::new_left`].
///
/// Creates a left associative infix operator that is parsed with the
/// parser `P`, and a function which is used to `build` a value `E`.
/// The operator's precedence is determined by `strength`. The higher
/// the value, the higher the precedence.
pub fn left_infix<P, E, PO>(parser: P, strength: u8, build: InfixBuilder<E>) -> InfixOp<P, E, PO> {
    InfixOp::new_left(parser, strength, build)
}

/// Shorthand for [`InfixOp::new_right`].
///
/// Creates a right associative infix operator that is parsed with the
/// parser `P`, and a function which is used to `build` a value `E`.
/// The operator's precedence is determined by `strength`. The higher
/// the value, the higher the precedence.
pub fn right_infix<P, E, PO>(parser: P, strength: u8, build: InfixBuilder<E>) -> InfixOp<P, E, PO> {
    InfixOp::new_right(parser, strength, build)
}

/// Shorthand for [`PrefixOp::new`].
///
/// Creates a prefix operator (a right-associative unary operator)
/// that is parsed with the parser `P`, and a function which is used
/// to `build` a value `E`. The operator's precedence is determined
/// by `strength`. The higher the value, the higher the precedence.
pub fn prefix<P, E, PO>(parser: P, strength: u8, build: PrefixBuilder<E>) -> PrefixOp<P, E, PO> {
    PrefixOp::new(parser, strength, build)
}

/// Shorthand for [`PostfixOp::new`].
///
/// Creates a postfix operator (a left-associative unary operator)
/// that is parsed with the parser `P`, and a function which is used
/// to `build` a value `E`. The operator's precedence is determined
/// by `strength`. The higher the value, the higher the precedence.
pub fn postfix<P, E, PO>(parser: P, strength: u8, build: PostfixBuilder<E>) -> PostfixOp<P, E, PO> {
    PostfixOp::new(parser, strength, build)
}

/// A struct which represents a parser capable of using pratt-parsing.
///
/// This parser contains a parser of type `Atom`, which parses expressions
/// are separated by a set of operators of parsed by a parser of type `Ops`.
/// The operators may have varying precedence levels, as well as associativity.
/// For those unfamiliar with operator precedence and/or associativity, it may
/// be helpful to read [this documentation](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Operators/Operator_Precedence)
///
/// This struct offers two methods:
/// * `with_prefix_ops`: Attaches prefix operators to the parser
/// * `with_postfix_ops`: Attaches postfix operators to the parser
///
/// Once one of the methods has been used, it will become unavailable
/// due to the use of the type-state pattern to prevent accidental
/// resetting of the operators.
/// See [`Parser::pratt`] for an example of how to use these methods.
#[derive(Copy, Clone)]
pub struct Pratt<I, O, E, Atom, Ops> {
    pub(crate) atom: Atom,
    pub(crate) ops: Ops,
    pub(crate) phantom: PhantomData<(I, O, E)>,
}

impl<'a, I, O, E, Atom, InfixOps, InfixOpsOut> Pratt<I, O, E, Atom, Infix<InfixOps, InfixOpsOut>> {
    /// Extend a `Pratt` parser by setting prefix operators.
    /// See [`Parser::pratt`] for an example of how to use this methods.
    pub fn with_prefix_ops<PrefixOps, PrefixOpsOut>(
        self,
        prefix_ops: PrefixOps,
    ) -> Pratt<I, O, E, Atom, InfixPrefix<InfixOps, InfixOpsOut, PrefixOps, PrefixOpsOut>>
    where
        I: Input<'a>,
        E: ParserExtra<'a, I>,
        InfixOps: Parser<'a, I, InfixOpsOut, E>,
        PrefixOps: Parser<'a, I, PrefixOpsOut, E>,
        Pratt<I, O, E, Atom, InfixPrefix<InfixOps, InfixOpsOut, PrefixOps, PrefixOpsOut>>:
            PrattParser<'a, I, O, E>,
    {
        Pratt {
            atom: self.atom,
            ops: InfixPrefix {
                infix: self.ops.infix,
                prefix: prefix_ops,
                phantom: PhantomData,
            },
            phantom: PhantomData,
        }
    }

    /// Extend a `Pratt` parser by setting postfix operators
    /// See [`Parser::pratt`] for an example of how to use this method.
    pub fn with_postfix_ops<PostfixOps, PostfixOpsOut>(
        self,
        postfix_ops: PostfixOps,
    ) -> Pratt<I, O, E, Atom, InfixPostfix<InfixOps, InfixOpsOut, PostfixOps, PostfixOpsOut>>
    where
        I: Input<'a>,
        E: ParserExtra<'a, I>,
        InfixOps: Parser<'a, I, InfixOpsOut, E>,
        PostfixOps: Parser<'a, I, PostfixOpsOut, E>,
        Pratt<I, O, E, Atom, InfixPostfix<InfixOps, InfixOpsOut, PostfixOps, PostfixOpsOut>>:
            PrattParser<'a, I, O, E>,
    {
        Pratt {
            atom: self.atom,
            ops: InfixPostfix {
                infix: self.ops.infix,
                postfix: postfix_ops,
                phantom: PhantomData,
            },
            phantom: PhantomData,
        }
    }
}

impl<'a, I, O, E, Atom, InfixOps, InfixOpsOut, PrefixOps, PrefixOpsOut>
    Pratt<I, O, E, Atom, InfixPrefix<InfixOps, InfixOpsOut, PrefixOps, PrefixOpsOut>>
{
    /// Extend a `Pratt` parser by setting postfix operators
    pub fn with_postfix_ops<PostfixOps, PostfixOpsOut>(
        self,
        postfix_ops: PostfixOps,
    ) -> Pratt<
        I,
        O,
        E,
        Atom,
        InfixPrefixPostfix<
            InfixOps,
            InfixOpsOut,
            PrefixOps,
            PrefixOpsOut,
            PostfixOps,
            PostfixOpsOut,
        >,
    >
    where
        I: Input<'a>,
        E: ParserExtra<'a, I>,
        InfixOps: Parser<'a, I, InfixOpsOut, E>,
        PrefixOps: Parser<'a, I, PrefixOpsOut, E>,
        PostfixOps: Parser<'a, I, PostfixOpsOut, E>,
        Pratt<
            I,
            O,
            E,
            Atom,
            InfixPrefixPostfix<
                InfixOps,
                InfixOpsOut,
                PrefixOps,
                PrefixOpsOut,
                PostfixOps,
                PostfixOpsOut,
            >,
        >: PrattParser<'a, I, O, E>,
    {
        Pratt {
            atom: self.atom,
            ops: InfixPrefixPostfix {
                infix: self.ops.infix,
                prefix: self.ops.prefix,
                postfix: postfix_ops,
                phantom: PhantomData,
            },
            phantom: PhantomData,
        }
    }
}

impl<'a, I, O, E, Atom, InfixOps, InfixOpsOut, PostfixOps, PostfixOpsOut>
    Pratt<I, O, E, Atom, InfixPostfix<InfixOps, InfixOpsOut, PostfixOps, PostfixOpsOut>>
{
    /// Extend a `Pratt` parser by setting prefix operators
    pub fn with_prefix_ops<PrefixOps, PrefixOpsOut>(
        self,
        prefix_ops: PrefixOps,
    ) -> Pratt<
        I,
        O,
        E,
        Atom,
        InfixPrefixPostfix<
            InfixOps,
            InfixOpsOut,
            PrefixOps,
            PrefixOpsOut,
            PostfixOps,
            PostfixOpsOut,
        >,
    >
    where
        I: Input<'a>,
        E: ParserExtra<'a, I>,
        PrefixOps: Parser<'a, I, PrefixOpsOut, E>,
    {
        Pratt {
            atom: self.atom,
            ops: InfixPrefixPostfix {
                infix: self.ops.infix,
                prefix: prefix_ops,
                postfix: self.ops.postfix,
                phantom: PhantomData,
            },
            phantom: PhantomData,
        }
    }
}

type InfixBuilder<E> = fn(lhs: E, rhs: E) -> E;

type PrefixBuilder<E> = fn(rhs: E) -> E;

type PostfixBuilder<E> = fn(rhs: E) -> E;

/// Privitize me you coward!
pub trait PrattParser<'a, I, Expr, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    /// This function drives the [`Pratt`] parser.
    fn pratt_parse<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        min_strength: Option<Strength>,
    ) -> PResult<M, Expr>;
}

impl<'a, I, O, E, Atom, InfixOps, InfixOpsOut> PrattParser<'a, I, O, E>
    for Pratt<I, O, E, Atom, Infix<InfixOps, InfixOpsOut>>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    Atom: Parser<'a, I, O, E>,
    InfixOps: Parser<'a, I, PrattOpOutput<InfixBuilder<O>>, E>,
{
    fn pratt_parse<M>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        min_strength: Option<Strength>,
    ) -> PResult<M, O>
    where
        M: Mode,
    {
        let mut left = self.atom.go::<M>(inp)?;
        loop {
            let pre_op = inp.save();
            let (op, prec) = match self.ops.infix.go::<Emit>(inp) {
                Ok(PrattOpOutput(prec, build)) => {
                    if prec.strength_left().is_lt(&min_strength) {
                        inp.rewind(pre_op);
                        return Ok(left);
                    }
                    (build, prec)
                }
                Err(_) => {
                    inp.rewind(pre_op);
                    return Ok(left);
                }
            };

            let right = self.pratt_parse::<M>(inp, Some(prec.strength_right()))?;
            left = M::combine(left, right, op);
        }
    }
}

impl<'a, I, O, E, Atom, InfixOps, InfixOpsOut, PrefixOps, PrefixOpsOut> PrattParser<'a, I, O, E>
    for Pratt<I, O, E, Atom, InfixPrefix<InfixOps, InfixOpsOut, PrefixOps, PrefixOpsOut>>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    Atom: Parser<'a, I, O, E>,
    InfixOps: Parser<'a, I, PrattOpOutput<InfixBuilder<O>>, E>,
    PrefixOps: Parser<'a, I, PrattOpOutput<PrefixBuilder<O>>, E>,
{
    fn pratt_parse<M>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        min_strength: Option<Strength>,
    ) -> PResult<M, O>
    where
        M: Mode,
    {
        let pre_op = inp.save();
        let mut left = match self.ops.prefix.go::<Emit>(inp) {
            Ok(PrattOpOutput(prec, build)) => {
                let right = self.pratt_parse::<M>(inp, Some(prec.strength_right()))?;
                M::map(right, build)
            }
            Err(_) => {
                inp.rewind(pre_op);
                self.atom.go::<M>(inp)?
            }
        };

        loop {
            let pre_op = inp.save();
            let (op, prec) = match self.ops.infix.go::<Emit>(inp) {
                Ok(PrattOpOutput(prec, build)) => {
                    if prec.strength_left().is_lt(&min_strength) {
                        inp.rewind(pre_op);
                        return Ok(left);
                    }
                    (build, prec)
                }
                Err(_) => {
                    inp.rewind(pre_op);
                    return Ok(left);
                }
            };

            let right = self.pratt_parse::<M>(inp, Some(prec.strength_right()))?;
            left = M::combine(left, right, op);
        }
    }
}

impl<'a, I, O, E, Atom, InfixOps, InfixOpsOut, PostfixOps, PostfixOpsOut> PrattParser<'a, I, O, E>
    for Pratt<I, O, E, Atom, InfixPostfix<InfixOps, InfixOpsOut, PostfixOps, PostfixOpsOut>>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    Atom: Parser<'a, I, O, E>,
    InfixOps: Parser<'a, I, PrattOpOutput<InfixBuilder<O>>, E>,
    PostfixOps: Parser<'a, I, PrattOpOutput<PostfixBuilder<O>>, E>,
{
    fn pratt_parse<M>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        min_strength: Option<Strength>,
    ) -> PResult<M, O>
    where
        M: Mode,
    {
        let mut left = self.atom.go::<M>(inp)?;
        loop {
            let pre_op = inp.save();
            match self.ops.postfix.go::<Emit>(inp) {
                Ok(PrattOpOutput(prec, build)) => {
                    if prec.strength_left().is_lt(&min_strength) {
                        inp.rewind(pre_op);
                        return Ok(left);
                    }
                    left = M::map(left, build);
                    continue;
                }
                Err(_) => {
                    inp.rewind(pre_op);
                }
            }

            let (op, prec) = match self.ops.infix.go::<Emit>(inp) {
                Ok(PrattOpOutput(prec, build)) => {
                    if prec.strength_left().is_lt(&min_strength) {
                        inp.rewind(pre_op);
                        return Ok(left);
                    }
                    (build, prec)
                }
                Err(_) => {
                    inp.rewind(pre_op);
                    return Ok(left);
                }
            };

            let right = self.pratt_parse::<M>(inp, Some(prec.strength_right()))?;
            left = M::combine(left, right, op);
        }
    }
}

impl<
        'a,
        I,
        O,
        E,
        Atom,
        InfixOps,
        InfixOpsOut,
        PrefixOps,
        PrefixOpsOut,
        PostfixOps,
        PostfixOpsOut,
    > PrattParser<'a, I, O, E>
    for Pratt<
        I,
        O,
        E,
        Atom,
        InfixPrefixPostfix<
            InfixOps,
            InfixOpsOut,
            PrefixOps,
            PrefixOpsOut,
            PostfixOps,
            PostfixOpsOut,
        >,
    >
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    Atom: Parser<'a, I, O, E>,
    InfixOps: Parser<'a, I, PrattOpOutput<InfixBuilder<O>>, E>,
    PrefixOps: Parser<'a, I, PrattOpOutput<PrefixBuilder<O>>, E>,
    PostfixOps: Parser<'a, I, PrattOpOutput<PostfixBuilder<O>>, E>,
{
    fn pratt_parse<M>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        min_strength: Option<Strength>,
    ) -> PResult<M, O>
    where
        M: Mode,
    {
        let pre_op = inp.save();
        let mut left = match self.ops.prefix.go::<Emit>(inp) {
            Ok(PrattOpOutput(prec, build)) => {
                let right = self.pratt_parse::<M>(inp, Some(prec.strength_right()))?;
                M::map(right, build)
            }
            Err(_) => {
                inp.rewind(pre_op);
                self.atom.go::<M>(inp)?
            }
        };

        loop {
            let pre_op = inp.save();
            match self.ops.postfix.go::<Emit>(inp) {
                Ok(PrattOpOutput(prec, build)) => {
                    if prec.strength_left().is_lt(&min_strength) {
                        inp.rewind(pre_op);
                        return Ok(left);
                    }
                    left = M::map(left, build);
                    continue;
                }
                Err(_) => {
                    inp.rewind(pre_op);
                }
            }

            let (op, prec) = match self.ops.infix.go::<Emit>(inp) {
                Ok(PrattOpOutput(prec, build)) => {
                    if prec.strength_left().is_lt(&min_strength) {
                        inp.rewind(pre_op);
                        return Ok(left);
                    }
                    (build, prec)
                }
                Err(_) => {
                    inp.rewind(pre_op);
                    return Ok(left);
                }
            };

            let right = self.pratt_parse::<M>(inp, Some(prec.strength_right()))?;
            left = M::combine(left, right, op);
        }
    }
}

macro_rules! impl_parse {
    ($Parser:ident < $($Gen:ident),+ $(,)?>) => {
        impl<'a, I, O, E, Atom, $($Gen),+> ParserSealed<'a, I, O, E> for Pratt<I, O, E, Atom, $Parser<$($Gen),+>>
        where
            I: Input<'a>,
            E: ParserExtra<'a, I>,
            Atom: Parser<'a, I, O, E>,
            Self: PrattParser<'a, I, O, E>,
        {
            fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O>
            where
                Self: Sized,
            {
                self.pratt_parse::<M>(inp, None)
            }

            go_extra!(O);
        }
    };
}

impl_parse!(Infix<InfixOps, InfixOpsOut>);

impl_parse!(InfixPrefix<InfixOps, InfixOpsOut, PrefixOps, PrefixOpsOut>);

impl_parse!(InfixPostfix<InfixOps, InfixOpsOut, PostfixOps, PostfixOpsOut>);

impl_parse!(InfixPrefixPostfix<InfixOps, InfixOpsOut, PrefixOps, PrefixOpsOut, PostfixOps, PostfixOpsOut,>);

#[cfg(test)]
mod tests {
    use crate::error::Error;
    use crate::extra::Err;
    use crate::prelude::{choice, end, just, Simple, SimpleSpan};
    use crate::util::MaybeRef;
    use crate::{text, ParseResult};

    use super::*;

    enum Expr {
        Literal(i64),
        Not(Box<Expr>),
        Negate(Box<Expr>),
        Confusion(Box<Expr>),
        Factorial(Box<Expr>),
        Value(Box<Expr>),
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
                Self::Add(left, right) => write!(f, "({left} + {right})"),
                Self::Sub(left, right) => write!(f, "({left} - {right})"),
                Self::Mul(left, right) => write!(f, "({left} * {right})"),
                Self::Div(left, right) => write!(f, "({left} / {right})"),
            }
        }
    }

    fn parser<'a>() -> impl Parser<'a, &'a str, String, Err<Simple<'a, char>>> {
        let atom = text::int(10).from_str().unwrapped().map(Expr::Literal);

        let operator = choice((
            left_infix(just('+'), 0, |l, r| Expr::Add(Box::new(l), Box::new(r))),
            left_infix(just('-'), 0, |l, r| Expr::Sub(Box::new(l), Box::new(r))),
            right_infix(just('*'), 1, |l, r| Expr::Mul(Box::new(l), Box::new(r))),
            right_infix(just('/'), 1, |l, r| Expr::Div(Box::new(l), Box::new(r))),
        ));

        atom.pratt(operator).map(|x| x.to_string())
    }

    fn complete_parser<'a>() -> impl Parser<'a, &'a str, String, Err<Simple<'a, char>>> {
        parser().then_ignore(end())
    }

    fn parse(input: &str) -> ParseResult<String, Simple<char>> {
        complete_parser().parse(input)
    }

    fn parse_partial(input: &str) -> ParseResult<String, Simple<char>> {
        parser().lazy().parse(input)
    }

    fn unexpected<'a, C: Into<Option<MaybeRef<'a, char>>>, S: Into<SimpleSpan>>(
        c: C,
        span: S,
    ) -> Simple<'a, char> {
        <Simple<_> as Error<'_, &'_ str>>::expected_found(None, c.into(), span.into())
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
        let atom = text::int::<_, _, Err<Simple<char>>>(10)
            .from_str()
            .unwrapped()
            .map(Expr::Literal);

        let operator = choice((
            left_infix(just('+'), 0, |l, r| Expr::Add(Box::new(l), Box::new(r))),
            left_infix(just('-'), 0, |l, r| Expr::Sub(Box::new(l), Box::new(r))),
            right_infix(just('*'), 1, |l, r| Expr::Mul(Box::new(l), Box::new(r))),
            right_infix(just('/'), 1, |l, r| Expr::Div(Box::new(l), Box::new(r))),
        ));

        let parser = atom
            .pratt(operator)
            .with_prefix_ops(choice((
                // Because we defined '*' and '/' as right associative operators,
                // in order to get these to function as expected, their strength
                // must be higher
                prefix(just('-'), 2, |rhs| Expr::Negate(Box::new(rhs))),
                prefix(just('~'), 2, |rhs| Expr::Not(Box::new(rhs))),
                // This is what happens when not
                prefix(just('§'), 1, |rhs| Expr::Confusion(Box::new(rhs))),
            )))
            .map(|x| x.to_string());

        assert_eq!(
            parser.parse("-1+§~2*3").into_result(),
            Ok("((-1) + (§((~2) * 3)))".to_string()),
        )
    }

    #[test]
    fn with_postfix_ops() {
        let atom = text::int::<_, _, Err<Simple<char>>>(10)
            .from_str()
            .unwrapped()
            .map(Expr::Literal);

        let operator = choice((
            left_infix(just('+'), 1, |l, r| Expr::Add(Box::new(l), Box::new(r))),
            left_infix(just('-'), 1, |l, r| Expr::Sub(Box::new(l), Box::new(r))),
            right_infix(just('*'), 2, |l, r| Expr::Mul(Box::new(l), Box::new(r))),
            right_infix(just('/'), 2, |l, r| Expr::Div(Box::new(l), Box::new(r))),
        ));

        let parser = atom
            .pratt(operator)
            .with_postfix_ops(choice((
                // Because we defined '+' and '-' as left associative operators,
                // in order to get these to function as expected, their strength
                // must be higher, i.e. they must bind tighter
                postfix(just('!'), 2, |lhs| Expr::Factorial(Box::new(lhs))),
                // Or weirdness happens
                postfix(just('$'), 0, |lhs| Expr::Value(Box::new(lhs))),
            )))
            .map(|x| x.to_string());

        assert_eq!(
            parser.parse("1+2!$*3").into_result(),
            Ok("(((1 + (2!))$) * 3)".to_string()),
        )
    }

    #[test]
    fn with_pre_and_postfix_ops() {
        let atom = text::int::<_, _, Err<Simple<char>>>(10)
            .from_str()
            .unwrapped()
            .map(Expr::Literal);

        let operator = choice((
            left_infix(just('+'), 1, |l, r| Expr::Add(Box::new(l), Box::new(r))),
            left_infix(just('-'), 1, |l, r| Expr::Sub(Box::new(l), Box::new(r))),
            right_infix(just('*'), 2, |l, r| Expr::Mul(Box::new(l), Box::new(r))),
            right_infix(just('/'), 2, |l, r| Expr::Div(Box::new(l), Box::new(r))),
        ));

        let parser = atom
            .pratt(operator)
            .with_prefix_ops(choice((
                // Because we defined '*' and '/' as right associative operators,
                // in order to get these to function as expected, their strength
                // must be higher
                prefix(just('-'), 4, |rhs| Expr::Negate(Box::new(rhs))),
                prefix(just('~'), 4, |rhs| Expr::Not(Box::new(rhs))),
                // This is what happens when not
                prefix(just('§'), 1, |rhs| Expr::Confusion(Box::new(rhs))),
            )))
            .with_postfix_ops(choice((
                // Because we defined '+' and '-' as left associative operators,
                // in order to get these to function as expected, their strength
                // must be higher, i.e. they must bind tighter
                postfix(just('!'), 5, |lhs| Expr::Factorial(Box::new(lhs))),
                // Or weirdness happens
                postfix(just('$'), 0, |lhs| Expr::Value(Box::new(lhs))),
            )))
            .map(|x| x.to_string());

        assert_eq!(
            parser.parse("§1+-~2!$*3").into_result(),
            Ok("(((§(1 + (-(~(2!)))))$) * 3)".to_string()),
        )
    }
}
