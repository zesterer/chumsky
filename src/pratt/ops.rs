use super::*;
use crate::EmptyPhantom;

pub struct PrattOpOutput<Builder>(pub(super) Precedence, pub(super) Builder);

pub struct Infix<P, PO> {
    pub(crate) infix: P,
    pub(crate) _phantom: EmptyPhantom<PO>,
}

pub struct InfixPrefix<P1, P1O, P2, P2O> {
    pub(crate) infix: P1,
    pub(crate) prefix: P2,
    pub(crate) _phantom: EmptyPhantom<(P1O, P2O)>,
}

pub struct InfixPostfix<P1, P1O, P2, P2O> {
    pub(crate) infix: P1,
    pub(crate) postfix: P2,
    pub(crate) _phantom: EmptyPhantom<(P1O, P2O)>,
}

pub struct InfixPrefixPostfix<P1, P1O, P2, P2O, P3, P3O> {
    pub(crate) infix: P1,
    pub(crate) prefix: P2,
    pub(crate) postfix: P3,
    pub(crate) _phantom: EmptyPhantom<(P1O, P2O, P3O)>,
}

impl<P, PO> Clone for Infix<P, PO>
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

impl<P1, P1O, P2, P2O> Clone for InfixPrefix<P1, P1O, P2, P2O>
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

impl<P1, P1O, P2, P2O> Clone for InfixPostfix<P1, P1O, P2, P2O>
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

impl<P1, P1O, P2, P2O, P3, P3O> Clone for InfixPrefixPostfix<P1, P1O, P2, P2O, P3, P3O>
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
/// [`Pratt::pratt`](super::Pratt::pratt).
pub struct InfixOp<P, E, PO> {
    strength: u8,
    assoc: Assoc,
    parser: P,
    build: InfixBuilder<E>,
    _phantom: EmptyPhantom<(PO,)>,
}

impl<P: Clone, E, PO> Clone for InfixOp<P, E, PO> {
    fn clone(&self) -> Self {
        Self {
            strength: self.strength,
            assoc: self.assoc,
            parser: self.parser.clone(),
            build: self.build,
            _phantom: EmptyPhantom::new(),
        }
    }
}

impl<P, E, PO> InfixOp<P, E, PO> {
    /// Creates a left associative infix operator that is parsed with the
    /// parser `P`, and a function which is used to `build` a value `E`.
    /// The operator's precedence is determined by `strength`. The higher
    /// the value, the higher the precedence.
    pub fn new_left(parser: P, strength: u8, build: InfixBuilder<E>) -> Self {
        Self {
            strength,
            assoc: Assoc::Left,
            parser,
            build,
            _phantom: EmptyPhantom::new(),
        }
    }

    /// Creates a right associative infix operator that is parsed with the
    /// parser `P`, and a function which is used to `build` a value `E`.
    /// The operator's precedence is determined by `strength`. The higher
    /// the value, the higher the precedence.
    pub fn new_right(parser: P, strength: u8, build: InfixBuilder<E>) -> Self {
        Self {
            strength,
            assoc: Assoc::Right,
            parser,
            build,
            _phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, P, Expr, I, O, E> ParserSealed<'a, I, PrattOpOutput<InfixBuilder<Expr>>, E>
    for InfixOp<P, Expr, O>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    P: Parser<'a, I, O, E>,
{
    fn go<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<M, PrattOpOutput<InfixBuilder<Expr>>>
    where
        Self: Sized,
    {
        match self.parser.go::<Check>(inp) {
            Ok(()) => Ok(M::bind(|| {
                PrattOpOutput(Precedence::new(self.strength, self.assoc), self.build)
            })),
            Err(()) => Err(()),
        }
    }

    go_extra!(PrattOpOutput<InfixBuilder<Expr>>);
}

/// A representation of a prefix operator to be used in combination with
/// [`Pratt::pratt`](super::Pratt::pratt).
pub struct PrefixOp<Parser, Expr, ParserOut> {
    strength: u8,
    parser: Parser,
    build: PrefixBuilder<Expr>,
    _phantom: EmptyPhantom<(ParserOut,)>,
}

impl<Parser: Clone, Expr, ParserOut> Clone for PrefixOp<Parser, Expr, ParserOut> {
    fn clone(&self) -> Self {
        Self {
            strength: self.strength,
            parser: self.parser.clone(),
            build: self.build,
            _phantom: EmptyPhantom::new(),
        }
    }
}

impl<Parser, Expr, ParserOut> PrefixOp<Parser, Expr, ParserOut> {
    /// Creates a prefix operator (a right-associative unary operator)
    /// that is parsed with the parser `P`, and a function which is used
    /// to `build` a value `E`. The operator's precedence is determined
    /// by `strength`. The higher the value, the higher the precedence.
    pub fn new(parser: Parser, strength: u8, build: PrefixBuilder<Expr>) -> Self {
        Self {
            strength,
            parser,
            build,
            _phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, P, Expr, I, O, E> ParserSealed<'a, I, PrattOpOutput<PrefixBuilder<Expr>>, E>
    for PrefixOp<P, Expr, O>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    P: Parser<'a, I, O, E>,
{
    fn go<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<M, PrattOpOutput<PrefixBuilder<Expr>>>
    where
        Self: Sized,
    {
        match self.parser.go::<Check>(inp) {
            Ok(()) => Ok(M::bind(|| {
                PrattOpOutput(Precedence::new(self.strength, Assoc::Right), self.build)
            })),
            Err(()) => Err(()),
        }
    }

    go_extra!(PrattOpOutput<PrefixBuilder<Expr>>);
}

/// A representation of a postfix operator to be used in combination with
/// [`Pratt::pratt`](super::Pratt::pratt).
pub struct PostfixOp<Parser, Expr, ParserOut> {
    strength: u8,
    parser: Parser,
    build: PostfixBuilder<Expr>,
    _phantom: EmptyPhantom<(ParserOut,)>,
}

impl<Parser: Clone, Expr, ParserOut> Clone for PostfixOp<Parser, Expr, ParserOut> {
    fn clone(&self) -> Self {
        Self {
            strength: self.strength,
            parser: self.parser.clone(),
            build: self.build,
            _phantom: EmptyPhantom::new(),
        }
    }
}

impl<Parser, Expr, ParserOut> PostfixOp<Parser, Expr, ParserOut> {
    /// Creates a postfix operator (a left-associative unary operator)
    /// that is parsed with the parser `P`, and a function which is used
    /// to `build` a value `E`. The operator's precedence is determined
    /// by `strength`. The higher the value, the higher the precedence.
    pub fn new(parser: Parser, strength: u8, build: PostfixBuilder<Expr>) -> Self {
        Self {
            strength,
            parser,
            build,
            _phantom: EmptyPhantom::new(),
        }
    }
}

impl<'a, P, Expr, I, O, E> ParserSealed<'a, I, PrattOpOutput<PostfixBuilder<Expr>>, E>
    for PostfixOp<P, Expr, O>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    P: Parser<'a, I, O, E>,
{
    fn go<M: Mode>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
    ) -> PResult<M, PrattOpOutput<PostfixBuilder<Expr>>>
    where
        Self: Sized,
    {
        match self.parser.go::<Check>(inp) {
            Ok(()) => Ok(M::bind(|| {
                PrattOpOutput(Precedence::new(self.strength, Assoc::Right), self.build)
            })),
            Err(()) => Err(()),
        }
    }

    go_extra!(PrattOpOutput<PostfixBuilder<Expr>>);
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
