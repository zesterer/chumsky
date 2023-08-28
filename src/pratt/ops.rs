use super::*;
use crate::EmptyPhantom;

/// Internal output of a pratt parser.
pub struct PrattOpOutput<Op, Builder>(pub(super) Precedence, pub(super) Op, pub(super) Builder);

/// Infix parser and the type of the operator.
/// Implements a parser that outputs `PrattOpOutput`.
pub struct Infix<P, Op> {
    pub(crate) infix: P,
    pub(crate) _phantom: EmptyPhantom<Op>,
}

pub struct InfixPrefix<P1, Op1, P2, Op2> {
    pub(crate) infix: P1,
    pub(crate) prefix: P2,
    pub(crate) _phantom: EmptyPhantom<(Op1, Op2)>,
}

pub struct InfixPostfix<P1, Op1, P2, Op2> {
    pub(crate) infix: P1,
    pub(crate) postfix: P2,
    pub(crate) _phantom: EmptyPhantom<(Op1, Op2)>,
}

pub struct InfixPrefixPostfix<P1, Op1, P2, Op2, P3, Op3> {
    pub(crate) infix: P1,
    pub(crate) prefix: P2,
    pub(crate) postfix: P3,
    pub(crate) _phantom: EmptyPhantom<(Op1, Op2, Op3)>,
}

impl<P, Op> Clone for Infix<P, Op>
where
    P: Clone,
{
    fn clone(&self) -> Self {
        Self {
            infix: self.infix.clone(),
            _phantom: EmptyPhantom::new(),
        }
    }
}

impl<P1, Op1, P2, Op2> Clone for InfixPrefix<P1, Op1, P2, Op2>
where
    P1: Clone,
    P2: Clone,
{
    fn clone(&self) -> Self {
        Self {
            infix: self.infix.clone(),
            prefix: self.prefix.clone(),
            _phantom: EmptyPhantom::new(),
        }
    }
}

impl<P1, Op1, P2, Op2> Clone for InfixPostfix<P1, Op1, P2, Op2>
where
    P1: Clone,
    P2: Clone,
{
    fn clone(&self) -> Self {
        Self {
            infix: self.infix.clone(),
            postfix: self.postfix.clone(),
            _phantom: EmptyPhantom::new(),
        }
    }
}

impl<P1, Op1, P2, Op2, P3, Op3> Clone for InfixPrefixPostfix<P1, Op1, P2, Op2, P3, Op3>
where
    P1: Clone,
    P2: Clone,
    P3: Clone,
{
    fn clone(&self) -> Self {
        Self {
            infix: self.infix.clone(),
            prefix: self.prefix.clone(),
            postfix: self.postfix.clone(),
            _phantom: EmptyPhantom::new(),
        }
    }
}

/// A representation of an infix operator to be used in combination with
/// [`Parser::pratt`](super::Parser::pratt).
pub struct InfixOp<P, Op, O> {
    strength: u8,
    assoc: Assoc,
    parser: P,
    build: InfixBuilder<Op, O>,
}

impl<P: Clone, Op, O> Clone for InfixOp<P, Op, O> {
    fn clone(&self) -> Self {
        Self {
            strength: self.strength,
            assoc: self.assoc,
            parser: self.parser.clone(),
            build: self.build,
        }
    }
}

impl<P, Op, O> InfixOp<P, Op, O> {
    /// Creates a left associative infix operator that is parsed with the
    /// parser `P`, and a function which is used to `build` a value `E`.
    /// The operator's precedence is determined by `strength`. The higher
    /// the value, the higher the precedence.
    pub fn new_left(parser: P, strength: u8, build: InfixBuilder<Op, O>) -> Self {
        Self {
            strength,
            assoc: Assoc::Left,
            parser,
            build,
        }
    }

    /// Creates a right associative infix operator that is parsed with the
    /// parser `P`, and a function which is used to `build` a value `E`.
    /// The operator's precedence is determined by `strength`. The higher
    /// the value, the higher the precedence.
    pub fn new_right(parser: P, strength: u8, build: InfixBuilder<Op, O>) -> Self {
        Self {
            strength,
            assoc: Assoc::Right,
            parser,
            build,
        }
    }
}

impl<'a, P, I, Op, O, E> ParserSealed<'a, I, PrattOpOutput<Op, InfixBuilder<Op, O>>, E>
    for InfixOp<P, Op, O>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    P: Parser<'a, I, Op, E>,
{
    fn go<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<M, PrattOpOutput<Op, InfixBuilder<Op, O>>>
    where
        Self: Sized,
    {
        match self.parser.go::<M>(inp) {
            Ok(op) => Ok(M::map(op, |op| {
                PrattOpOutput(Precedence::new(self.strength, self.assoc), op, self.build)
            })),
            Err(()) => Err(()),
        }
    }

    go_extra!(PrattOpOutput<Op, InfixBuilder<Op, O>>);
}

/// A representation of a prefix operator to be used in combination with
/// [`Parser::pratt`](super::Parser::pratt).
pub struct PrefixOp<Parser, Op, O> {
    strength: u8,
    parser: Parser,
    build: PrefixBuilder<Op, O>,
}

impl<Parser: Clone, Op, O> Clone for PrefixOp<Parser, Op, O> {
    fn clone(&self) -> Self {
        Self {
            strength: self.strength,
            parser: self.parser.clone(),
            build: self.build,
        }
    }
}

impl<Parser, Op, O> PrefixOp<Parser, Op, O> {
    /// Creates a prefix operator (a right-associative unary operator)
    /// that is parsed with the parser `P`, and a function which is used
    /// to `build` a value `E`. The operator's precedence is determined
    /// by `strength`. The higher the value, the higher the precedence.
    pub fn new(parser: Parser, strength: u8, build: PrefixBuilder<Op, O>) -> Self {
        Self {
            strength,
            parser,
            build,
        }
    }
}

impl<'a, P, I, Op, O, E> ParserSealed<'a, I, PrattOpOutput<Op, PrefixBuilder<Op, O>>, E>
    for PrefixOp<P, Op, O>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    P: Parser<'a, I, Op, E>,
{
    fn go<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<M, PrattOpOutput<Op, PrefixBuilder<Op, O>>>
    where
        Self: Sized,
    {
        match self.parser.go::<M>(inp) {
            Ok(op) => Ok(M::map(op, |op| {
                PrattOpOutput(Precedence::new(self.strength, Assoc::Right), op, self.build)
            })),
            Err(()) => Err(()),
        }
    }

    go_extra!(PrattOpOutput<Op, PrefixBuilder<Op, O>>);
}

/// A representation of a postfix operator to be used in combination with
/// [`Parser::pratt`](super::Parser::pratt).
pub struct PostfixOp<Parser, Op, O> {
    strength: u8,
    parser: Parser,
    build: PostfixBuilder<Op, O>,
}

impl<Parser: Clone, Op, O> Clone for PostfixOp<Parser, Op, O> {
    fn clone(&self) -> Self {
        Self {
            strength: self.strength,
            parser: self.parser.clone(),
            build: self.build,
        }
    }
}

impl<Parser, Op, O> PostfixOp<Parser, Op, O> {
    /// Creates a postfix operator (a left-associative unary operator)
    /// that is parsed with the parser `P`, and a function which is used
    /// to `build` a value `E`. The operator's precedence is determined
    /// by `strength`. The higher the value, the higher the precedence.
    pub fn new(parser: Parser, strength: u8, build: PostfixBuilder<Op, O>) -> Self {
        Self {
            strength,
            parser,
            build,
        }
    }
}

impl<'a, P, I, Op, O, E> ParserSealed<'a, I, PrattOpOutput<Op, PostfixBuilder<Op, O>>, E>
    for PostfixOp<P, Op, O>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    P: Parser<'a, I, Op, E>,
{
    fn go<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<M, PrattOpOutput<Op, PostfixBuilder<Op, O>>>
    where
        Self: Sized,
    {
        match self.parser.go::<M>(inp) {
            Ok(op) => Ok(M::map(op, |op| {
                PrattOpOutput(Precedence::new(self.strength, Assoc::Right), op, self.build)
            })),
            Err(()) => Err(()),
        }
    }

    go_extra!(PrattOpOutput<Op, PostfixBuilder<Op, O>>);
}

/// Indicates which argument binds more strongly with a binary infix operator.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Assoc {
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
pub enum Strength {
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
    pub fn is_lt(&self, other: &Option<Self>) -> bool {
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
pub(super) struct Precedence {
    strength: u8,
    associativity: Assoc,
}

impl Precedence {
    /// Create a new precedence value.
    pub fn new(strength: u8, associativity: Assoc) -> Self {
        Self {
            strength,
            associativity,
        }
    }

    /// Get the binding power of this operator with an argument on the left.
    pub fn strength_left(&self) -> Strength {
        match self.associativity {
            Assoc::Left => Strength::Weak(self.strength),
            Assoc::Right => Strength::Strong(self.strength),
        }
    }

    /// Get the binding power of this operator with an argument on the right.
    pub fn strength_right(&self) -> Strength {
        match self.associativity {
            Assoc::Left => Strength::Strong(self.strength),
            Assoc::Right => Strength::Weak(self.strength),
        }
    }
}
