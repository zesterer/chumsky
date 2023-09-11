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

use core::cmp::{self, Ordering};

use crate::{
    extra::ParserExtra,
    input::InputRef,
    prelude::Input,
    private::{Check, Emit, Mode, PResult, ParserSealed},
    EmptyPhantom, Parser,
};

pub(super) use ops::{Infix, InfixPostfix, InfixPrefix, InfixPrefixPostfix, PrattOpOutput};

/// Shorthand for [`InfixOp::new_left`].
///
/// Creates a left associative infix operator that is parsed with the
/// parser `P`, and a function which is used to `build` a value `O`.
/// The operator's precedence is determined by `strength`. The higher
/// the value, the higher the precedence.
pub fn left_infix<P, Op, O>(
    parser: P,
    strength: u16,
    build: InfixBuilder<Op, O>,
) -> InfixOp<P, Op, O> {
    InfixOp::new_left(parser, strength, build)
}

/// Shorthand for [`InfixOp::new_right`].
///
/// Creates a right associative infix operator that is parsed with the
/// parser `P`, and a function which is used to `build` a value `O`.
/// The operator's precedence is determined by `strength`. The higher
/// the value, the higher the precedence.
pub fn right_infix<P, Op, O>(
    parser: P,
    strength: u16,
    build: InfixBuilder<Op, O>,
) -> InfixOp<P, Op, O> {
    InfixOp::new_right(parser, strength, build)
}

/// Shorthand for [`PrefixOp::new`].
///
/// Creates a prefix operator (a right-associative unary operator)
/// that is parsed with the parser `P`, and a function which is used
/// to `build` a value `O`. The operator's precedence is determined
/// by `strength`. The higher the value, the higher the precedence.
pub fn prefix<P, Op, O>(
    parser: P,
    strength: u16,
    build: PrefixBuilder<Op, O>,
) -> PrefixOp<P, Op, O> {
    PrefixOp::new(parser, strength, build)
}

/// Shorthand for [`PostfixOp::new`].
///
/// Creates a postfix operator (a left-associative unary operator)
/// that is parsed with the parser `P`, and a function which is used
/// to `build` a value `O`. The operator's precedence is determined
/// by `strength`. The higher the value, the higher the precedence.
pub fn postfix<P, Op, O>(
    parser: P,
    strength: u16,
    build: PostfixBuilder<Op, O>,
) -> PostfixOp<P, Op, O> {
    PostfixOp::new(parser, strength, build)
}

/// A struct which represents a parser capable of using pratt-parsing.
///
/// This parser contains a parser of type `Atom`, which parses expressions that
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
pub struct Pratt<I, O, E, Atom, Ops> {
    pub(crate) atom: Atom,
    pub(crate) ops: Ops,
    pub(crate) _phantom: EmptyPhantom<(I, O, E)>,
}

impl<I, O, E, Atom, Ops> Copy for Pratt<I, O, E, Atom, Ops>
where
    Atom: Copy,
    Ops: Copy,
{
}

impl<I, O, E, Atom, Ops> Clone for Pratt<I, O, E, Atom, Ops>
where
    Atom: Clone,
    Ops: Clone,
{
    fn clone(&self) -> Self {
        Self {
            atom: self.atom.clone(),
            ops: self.ops.clone(),
            _phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, O, E, Atom, InfixParser, InfixOperator>
    Pratt<I, O, E, Atom, Infix<InfixParser, InfixOperator>>
{
    /// Extend a `Pratt` parser by setting prefix operators.
    /// See [`Parser::pratt`] for an example of how to use this methods.
    pub fn with_prefix_ops<PrefixParser, PrefixOperator>(
        self,
        prefix_ops: PrefixParser,
    ) -> Pratt<I, O, E, Atom, InfixPrefix<InfixParser, InfixOperator, PrefixParser, PrefixOperator>>
    where
        I: Input<'a>,
        E: ParserExtra<'a, I>,
        Pratt<I, O, E, Atom, InfixPrefix<InfixParser, InfixOperator, PrefixParser, PrefixOperator>>:
            PrattParser<'a, I, O, E>,
    {
        Pratt {
            atom: self.atom,
            ops: InfixPrefix {
                infix: self.ops.infix,
                prefix: prefix_ops,
                _phantom: EmptyPhantom::new(),
            },
            _phantom: EmptyPhantom::new(),
        }
    }

    /// Extend a `Pratt` parser by setting postfix operators
    /// See [`Parser::pratt`] for an example of how to use this method.
    pub fn with_postfix_ops<PostfixParser, PostfixOperator>(
        self,
        postfix_ops: PostfixParser,
    ) -> Pratt<
        I,
        O,
        E,
        Atom,
        InfixPostfix<InfixParser, InfixOperator, PostfixParser, PostfixOperator>,
    >
    where
        I: Input<'a>,
        E: ParserExtra<'a, I>,
        Pratt<
            I,
            O,
            E,
            Atom,
            InfixPostfix<InfixParser, InfixOperator, PostfixParser, PostfixOperator>,
        >: PrattParser<'a, I, O, E>,
    {
        Pratt {
            atom: self.atom,
            ops: InfixPostfix {
                infix: self.ops.infix,
                postfix: postfix_ops,
                _phantom: EmptyPhantom::new(),
            },
            _phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, O, E, Atom, InfixParser, InfixOperator, PrefixParser, PrefixOperator>
    Pratt<I, O, E, Atom, InfixPrefix<InfixParser, InfixOperator, PrefixParser, PrefixOperator>>
{
    /// Extend a `Pratt` parser by setting postfix operators
    pub fn with_postfix_ops<PostfixParser, PostfixOperator>(
        self,
        postfix_ops: PostfixParser,
    ) -> Pratt<
        I,
        O,
        E,
        Atom,
        InfixPrefixPostfix<
            InfixParser,
            InfixOperator,
            PrefixParser,
            PrefixOperator,
            PostfixParser,
            PostfixOperator,
        >,
    >
    where
        I: Input<'a>,
        E: ParserExtra<'a, I>,
        Pratt<
            I,
            O,
            E,
            Atom,
            InfixPrefixPostfix<
                InfixParser,
                InfixOperator,
                PrefixParser,
                PrefixOperator,
                PostfixParser,
                PostfixOperator,
            >,
        >: PrattParser<'a, I, O, E>,
    {
        Pratt {
            atom: self.atom,
            ops: InfixPrefixPostfix {
                infix: self.ops.infix,
                prefix: self.ops.prefix,
                postfix: postfix_ops,
                _phantom: EmptyPhantom::new(),
            },
            _phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, I, O, E, Atom, InfixParser, InfixOperator, PostfixParser, PostfixOperator>
    Pratt<I, O, E, Atom, InfixPostfix<InfixParser, InfixOperator, PostfixParser, PostfixOperator>>
{
    /// Extend a `Pratt` parser by setting prefix operators
    pub fn with_prefix_ops<PrefixParser, PrefixOperator>(
        self,
        prefix_ops: PrefixParser,
    ) -> Pratt<
        I,
        O,
        E,
        Atom,
        InfixPrefixPostfix<
            InfixParser,
            InfixOperator,
            PrefixParser,
            PrefixOperator,
            PostfixParser,
            PostfixOperator,
        >,
    >
    where
        I: Input<'a>,
        E: ParserExtra<'a, I>,
    {
        Pratt {
            atom: self.atom,
            ops: InfixPrefixPostfix {
                infix: self.ops.infix,
                prefix: prefix_ops,
                postfix: self.ops.postfix,
                _phantom: EmptyPhantom::new(),
            },
            _phantom: EmptyPhantom::new(),
        }
    }
}

type InfixBuilder<Op, O> = fn(op: Op, children: [O; 2]) -> O;

type PrefixBuilder<Op, O> = fn(op: Op, child: O) -> O;

type PostfixBuilder<Op, O> = fn(op: Op, child: O) -> O;

mod nameless_trait {
    use super::*;

    pub trait PrattParser<'a, I, Expr, E>
    where
        I: Input<'a>,
        E: ParserExtra<'a, I>,
    {
        fn pratt_parse<M: Mode>(
            &self,
            inp: &mut InputRef<'a, '_, I, E>,
            min_strength: Option<Strength>,
        ) -> PResult<M, Expr>;
    }
}

use nameless_trait::PrattParser;

impl<'a, I, O, E, Atom, InfixParser, InfixOperator> PrattParser<'a, I, O, E>
    for Pratt<I, O, E, Atom, Infix<InfixParser, InfixOperator>>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    Atom: Parser<'a, I, O, E>,
    InfixParser: Parser<'a, I, PrattOpOutput<InfixOperator, InfixBuilder<InfixOperator, O>>, E>,
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
            let (prec, op, build) = match self.ops.infix.go::<Emit>(inp) {
                Ok(PrattOpOutput(prec, op, build)) => {
                    if prec.strength_left().is_lt(&min_strength) {
                        inp.rewind(pre_op);
                        return Ok(left);
                    }
                    (prec, op, build)
                }
                Err(_) => {
                    inp.rewind(pre_op);
                    return Ok(left);
                }
            };

            let right = self.pratt_parse::<M>(inp, Some(prec.strength_right()))?;
            let children = M::array([left, right]);
            left = M::combine(M::bind(|| op), children, build);
        }
    }
}

impl<'a, I, O, E, Atom, InfixParser, InfixOperator, PrefixParser, PrefixOperator>
    PrattParser<'a, I, O, E>
    for Pratt<I, O, E, Atom, InfixPrefix<InfixParser, InfixOperator, PrefixParser, PrefixOperator>>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    Atom: Parser<'a, I, O, E>,
    InfixParser: Parser<'a, I, PrattOpOutput<InfixOperator, InfixBuilder<InfixOperator, O>>, E>,
    PrefixParser: Parser<'a, I, PrattOpOutput<PrefixOperator, PrefixBuilder<PrefixOperator, O>>, E>,
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
            Ok(PrattOpOutput(prec, op, build)) => {
                let right = self.pratt_parse::<M>(inp, Some(prec.strength_right()))?;
                M::combine(M::bind(|| op), right, build)
            }
            Err(_) => {
                inp.rewind(pre_op);
                self.atom.go::<M>(inp)?
            }
        };

        loop {
            let pre_op = inp.save();
            let (prec, op, build) = match self.ops.infix.go::<Emit>(inp) {
                Ok(PrattOpOutput(prec, op, build)) => {
                    if prec.strength_left().is_lt(&min_strength) {
                        inp.rewind(pre_op);
                        return Ok(left);
                    }
                    (prec, op, build)
                }
                Err(_) => {
                    inp.rewind(pre_op);
                    return Ok(left);
                }
            };

            let right = self.pratt_parse::<M>(inp, Some(prec.strength_right()))?;
            let children = M::array([left, right]);
            left = M::combine(M::bind(|| op), children, build);
        }
    }
}

impl<'a, I, O, E, Atom, InfixParser, InfixOperator, PostfixParser, PostfixOperator>
    PrattParser<'a, I, O, E>
    for Pratt<
        I,
        O,
        E,
        Atom,
        InfixPostfix<InfixParser, InfixOperator, PostfixParser, PostfixOperator>,
    >
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    Atom: Parser<'a, I, O, E>,
    InfixParser: Parser<'a, I, PrattOpOutput<InfixOperator, InfixBuilder<InfixOperator, O>>, E>,
    PostfixParser:
        Parser<'a, I, PrattOpOutput<PostfixOperator, PostfixBuilder<PostfixOperator, O>>, E>,
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
                Ok(PrattOpOutput(prec, op, build)) => {
                    if prec.strength_left().is_lt(&min_strength) {
                        inp.rewind(pre_op);
                        return Ok(left);
                    }
                    left = M::combine(M::bind(|| op), left, build);
                    continue;
                }
                Err(_) => {
                    inp.rewind(pre_op);
                }
            }

            let (prec, op, build) = match self.ops.infix.go::<Emit>(inp) {
                Ok(PrattOpOutput(prec, op, build)) => {
                    if prec.strength_left().is_lt(&min_strength) {
                        inp.rewind(pre_op);
                        return Ok(left);
                    }
                    (prec, op, build)
                }
                Err(_) => {
                    inp.rewind(pre_op);
                    return Ok(left);
                }
            };

            let right = self.pratt_parse::<M>(inp, Some(prec.strength_right()))?;
            let children = M::array([left, right]);
            left = M::combine(M::bind(|| op), children, build);
        }
    }
}

impl<
        'a,
        I,
        O,
        E,
        Atom,
        InfixParser,
        InfixOperator,
        PrefixParser,
        PrefixOperator,
        PostfixParser,
        PostfixOperator,
    > PrattParser<'a, I, O, E>
    for Pratt<
        I,
        O,
        E,
        Atom,
        InfixPrefixPostfix<
            InfixParser,
            InfixOperator,
            PrefixParser,
            PrefixOperator,
            PostfixParser,
            PostfixOperator,
        >,
    >
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    Atom: Parser<'a, I, O, E>,
    InfixParser: Parser<'a, I, PrattOpOutput<InfixOperator, InfixBuilder<InfixOperator, O>>, E>,
    PrefixParser: Parser<'a, I, PrattOpOutput<PrefixOperator, PrefixBuilder<PrefixOperator, O>>, E>,
    PostfixParser:
        Parser<'a, I, PrattOpOutput<PostfixOperator, PostfixBuilder<PostfixOperator, O>>, E>,
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
            Ok(PrattOpOutput(prec, op, build)) => {
                let right = self.pratt_parse::<M>(inp, Some(prec.strength_right()))?;
                M::combine(M::bind(|| op), right, build)
            }
            Err(_) => {
                inp.rewind(pre_op);
                self.atom.go::<M>(inp)?
            }
        };

        loop {
            let pre_op = inp.save();
            match self.ops.postfix.go::<Emit>(inp) {
                Ok(PrattOpOutput(prec, op, build)) => {
                    if prec.strength_left().is_lt(&min_strength) {
                        inp.rewind(pre_op);
                        return Ok(left);
                    }
                    left = M::combine(M::bind(|| op), left, build);
                    continue;
                }
                Err(_) => {
                    inp.rewind(pre_op);
                }
            }

            let (prec, op, build) = match self.ops.infix.go::<Emit>(inp) {
                Ok(PrattOpOutput(prec, op, build)) => {
                    if prec.strength_left().is_lt(&min_strength) {
                        inp.rewind(pre_op);
                        return Ok(left);
                    }
                    (prec, op, build)
                }
                Err(_) => {
                    inp.rewind(pre_op);
                    return Ok(left);
                }
            };

            let right = self.pratt_parse::<M>(inp, Some(prec.strength_right()))?;
            let children = M::array([left, right]);
            left = M::combine(M::bind(|| op), children, build);
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

impl_parse!(Infix<InfixParser, InfixOperator>);

impl_parse!(InfixPrefix<InfixParser, InfixOperator, PrefixParser, PrefixOperator>);

impl_parse!(InfixPostfix<InfixParser, InfixOperator, PostfixParser, PostfixOperator>);

impl_parse!(InfixPrefixPostfix<InfixParser, InfixOperator, PrefixParser, PrefixOperator, PostfixParser, PostfixOperator,>);

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
            left_infix(just('+'), 0, |_, [l, r]| {
                Expr::Add(Box::new(l), Box::new(r))
            }),
            left_infix(just('-'), 0, |_, [l, r]| {
                Expr::Sub(Box::new(l), Box::new(r))
            }),
            right_infix(just('*'), 1, |_, [l, r]| {
                Expr::Mul(Box::new(l), Box::new(r))
            }),
            right_infix(just('/'), 1, |_, [l, r]| {
                Expr::Div(Box::new(l), Box::new(r))
            }),
        ));

        let pratt = atom.pratt(operator);
        let pratt1 = pratt.map(|x| x.to_string());
        pratt1
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
            left_infix(just('+'), 0, |_op, [l, r]| {
                Expr::Add(Box::new(l), Box::new(r))
            }),
            left_infix(just('-'), 0, |_op, [l, r]| {
                Expr::Sub(Box::new(l), Box::new(r))
            }),
            right_infix(just('*'), 1, |_op, [l, r]| {
                Expr::Mul(Box::new(l), Box::new(r))
            }),
            right_infix(just('/'), 1, |_op, [l, r]| {
                Expr::Div(Box::new(l), Box::new(r))
            }),
        ));

        let parser = atom
            .pratt(operator)
            .with_prefix_ops(choice((
                // Because we defined '*' and '/' as right associative operators,
                // in order to get these to function as expected, their strength
                // must be higher
                prefix(just('-'), 2, |_op, rhs| Expr::Negate(Box::new(rhs))),
                prefix(just('~'), 2, |_op, rhs| Expr::Not(Box::new(rhs))),
                // This is what happens when not
                prefix(just('§'), 1, |_op, rhs| Expr::Confusion(Box::new(rhs))),
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
            left_infix(just('+'), 1, |_op, [l, r]| {
                Expr::Add(Box::new(l), Box::new(r))
            }),
            left_infix(just('-'), 1, |_op, [l, r]| {
                Expr::Sub(Box::new(l), Box::new(r))
            }),
            right_infix(just('*'), 2, |_op, [l, r]| {
                Expr::Mul(Box::new(l), Box::new(r))
            }),
            right_infix(just('/'), 2, |_op, [l, r]| {
                Expr::Div(Box::new(l), Box::new(r))
            }),
        ));

        let parser = atom
            .pratt(operator)
            .with_postfix_ops(choice((
                // Because we defined '+' and '-' as left associative operators,
                // in order to get these to function as expected, their strength
                // must be higher, i.e. they must bind tighter
                postfix(just('!'), 2, |_op, lhs| Expr::Factorial(Box::new(lhs))),
                // Or weirdness happens
                postfix(just('$'), 0, |_op, lhs| Expr::Value(Box::new(lhs))),
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
            left_infix(just('+'), 1, |_op, [l, r]| {
                Expr::Add(Box::new(l), Box::new(r))
            }),
            left_infix(just('-'), 1, |_op, [l, r]| {
                Expr::Sub(Box::new(l), Box::new(r))
            }),
            right_infix(just('*'), 2, |_op, [l, r]| {
                Expr::Mul(Box::new(l), Box::new(r))
            }),
            right_infix(just('/'), 2, |_op, [l, r]| {
                Expr::Div(Box::new(l), Box::new(r))
            }),
        ));

        let parser = atom
            .pratt(operator)
            .with_prefix_ops(choice((
                // Because we defined '*' and '/' as right associative operators,
                // in order to get these to function as expected, their strength
                // must be higher
                prefix(just('-'), 4, |_op, rhs| Expr::Negate(Box::new(rhs))),
                prefix(just('~'), 4, |_op, rhs| Expr::Not(Box::new(rhs))),
                // This is what happens when not
                prefix(just('§'), 1, |_op, rhs| Expr::Confusion(Box::new(rhs))),
            )))
            .with_postfix_ops(choice((
                // Because we defined '+' and '-' as left associative operators,
                // in order to get these to function as expected, their strength
                // must be higher, i.e. they must bind tighter
                postfix(just('!'), 5, |_op, lhs| Expr::Factorial(Box::new(lhs))),
                // Or weirdness happens
                postfix(just('$'), 0, |_op, lhs| Expr::Value(Box::new(lhs))),
            )))
            .map(|x| x.to_string());

        assert_eq!(
            parser.parse("§1+-~2!$*3").into_result(),
            Ok("(((§(1 + (-(~(2!)))))$) * 3)".to_string()),
        )
    }
}
