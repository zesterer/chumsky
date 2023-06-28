//! Pratt parser for binary infix operators.
//!
//! Pratt parsing is an algorithm that allows efficient
//! parsing of binary infix operators.
//!
//! The [`Parser::pratt`] method creates a Pratt parser.
//! Its documentation contains an example of how it can be used.

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

type ExprBuilder<E> = fn(lhs: E, rhs: E) -> E;

/// This type is only used so that InfixPrecedence doesn't have to be
/// public... it's a bit awkward.
pub struct PrattOpOutput<Expr>(InfixPrecedence, ExprBuilder<Expr>);

/// DOCUMENT
pub struct PrattOp<P, E, PO> {
    strength: u8,
    assoc: Assoc,
    parser: P,
    build: ExprBuilder<E>,
    phantom: PhantomData<(PO,)>,
}

impl<P: Clone, E, PO> Clone for PrattOp<P, E, PO> {
    fn clone(&self) -> Self {
        Self {
            strength: self.strength,
            assoc: self.assoc,
            parser: self.parser.clone(),
            build: self.build,
            phantom: PhantomData,
        }
    }
}

impl<P, E, PO> PrattOp<P, E, PO> {
    /// DOCUMENT
    pub fn new_left(parser: P, strength: u8, build: ExprBuilder<E>) -> Self {
        Self {
            strength,
            assoc: Assoc::Left,
            parser,
            build,
            phantom: PhantomData,
        }
    }

    /// DOCUMENT
    pub fn new_right(parser: P, strength: u8, build: ExprBuilder<E>) -> Self {
        Self {
            strength,
            assoc: Assoc::Right,
            parser,
            build,
            phantom: PhantomData,
        }
    }
}

impl<'a, P, Expr, I, O, E> ParserSealed<'a, I, PrattOpOutput<Expr>, E> for PrattOp<P, Expr, O>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    P: Parser<'a, I, O, E>,
{
    fn go<'b, M: Mode>(
        &'b self,
        inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<M, PrattOpOutput<Expr>>
    where
        Self: Sized,
    {
        match self.parser.go::<Check>(inp) {
            Ok(()) => Ok(M::bind(|| {
                PrattOpOutput(InfixPrecedence::new(self.strength, self.assoc), self.build)
            })),
            Err(()) => Err(()),
        }
    }

    go_extra!(PrattOpOutput<Expr>);
}

/// DOCUMENT
#[derive(Copy, Clone)]
pub struct Pratt<Atom, Ops, Expr, Op, Ex> {
    pub(crate) atom: Atom,
    pub(crate) ops: Ops,
    pub(crate) phantom: PhantomData<(Expr, Op, Ex)>,
}

impl<Atom, Ops, Expr, Op, Ex> Pratt<Atom, Ops, Expr, Op, Ex> {
    fn pratt_parse<'a, M, I>(
        &self,
        inp: &mut InputRef<'a, '_, I, Ex>,
        min_strength: Option<Strength>,
    ) -> PResult<M, Expr>
    where
        M: Mode,
        I: Input<'a>,
        Ex: ParserExtra<'a, I>,
        Atom: Parser<'a, I, Expr, Ex>,
        Ops: Parser<'a, I, PrattOpOutput<Expr>, Ex>,
    {
        let mut left = self.atom.go::<M>(inp)?;
        loop {
            let pre_op = inp.save();
            let (op, prec) = match self.ops.go::<Emit>(inp) {
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

            let right = self.pratt_parse::<M, _>(inp, Some(prec.strength_right()))?;
            left = M::combine(left, right, op);
        }
    }
}

impl<'a, I, Op, E, Expr, Atom, Ops> ParserSealed<'a, I, Expr, E> for Pratt<Atom, Ops, Expr, Op, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    Atom: Parser<'a, I, Expr, E>,
    Ops: Parser<'a, I, PrattOpOutput<Expr>, E>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, Expr>
    where
        Self: Sized,
    {
        self.pratt_parse::<M, _>(inp, None)
    }

    go_extra!(Expr);
}

/// Indicates which argument binds more strongly with a binary infix operator.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Assoc {
    /// The operator binds more strongly with the argument to the left.
    ///
    /// For example `a + b + c` is parsed as `(a + b) + c`.
    Left,

    /// The operator binds more strongly with the argument to the right.
    ///
    /// For example `a + b + c` is parsed as `a + (b + c)`.
    Right,
}

/// Indicates the binding strength of an operator to an argument.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Strength {
    /// This is the strongly associated side of the operator.
    Strong(u8),

    /// This is the weakly associated side of the operator.
    Weak(u8),
}

impl Strength {
    /// Get the binding strength, ignoring associativity.
    pub fn strength(&self) -> &u8 {
        match self {
            Self::Strong(strength) => strength,
            Self::Weak(strength) => strength,
        }
    }

    /// Compare two strengths.
    ///
    /// `None` is considered less strong than any `Some(Strength<T>)`,
    /// as it's used to indicate the lack of an operator
    /// to the left of the first expression and cannot bind.
    fn is_lt(&self, other: &Option<Self>) -> bool {
        match (self, other) {
            (x, Some(y)) => x < y,
            (_, None) => false,
        }
    }
}

impl PartialOrd for Strength {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match self.strength().partial_cmp(other.strength()) {
            Some(Ordering::Equal) => match (self, other) {
                (Self::Strong(_), Self::Weak(_)) => Some(cmp::Ordering::Greater),
                (Self::Weak(_), Self::Strong(_)) => Some(cmp::Ordering::Less),
                _ => Some(cmp::Ordering::Equal),
            },
            ord => ord,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct InfixPrecedence {
    strength: u8,
    associativity: Assoc,
}

impl InfixPrecedence {
    /// Create a new precedence value.
    pub fn new(strength: u8, associativity: Assoc) -> Self {
        Self {
            strength,
            associativity,
        }
    }
}

impl InfixPrecedence {
    /// Get the binding power of this operator with an argument on the left.
    fn strength_left(&self) -> Strength {
        match self.associativity {
            Assoc::Left => Strength::Weak(self.strength),
            Assoc::Right => Strength::Strong(self.strength),
        }
    }

    /// Get the binding power of this operator with an argument on the right.
    fn strength_right(&self) -> Strength {
        match self.associativity {
            Assoc::Left => Strength::Strong(self.strength),
            Assoc::Right => Strength::Weak(self.strength),
        }
    }
}
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
        Add(Box<Expr>, Box<Expr>),
        Sub(Box<Expr>, Box<Expr>),
        Mul(Box<Expr>, Box<Expr>),
        Div(Box<Expr>, Box<Expr>),
    }

    impl std::fmt::Display for Expr {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Self::Literal(literal) => write!(f, "{literal}"),
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
            PrattOp::new_left(just('+'), 0, |l, r| Expr::Add(Box::new(l), Box::new(r))),
            PrattOp::new_left(just('-'), 0, |l, r| Expr::Sub(Box::new(l), Box::new(r))),
            PrattOp::new_right(just('*'), 1, |l, r| Expr::Mul(Box::new(l), Box::new(r))),
            PrattOp::new_right(just('/'), 1, |l, r| Expr::Div(Box::new(l), Box::new(r))),
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
}
