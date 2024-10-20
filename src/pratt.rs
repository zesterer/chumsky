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
//! Fold functions have several overloads, allowing you to make use of only the operands, the operands and the
//! operators, and even additionally [`MapExtra`], providing access to the span, slice, and parser state. See the
//! documentation for each function to see which fold signatures can be used.
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
//! let atom = text::int::<_, _, extra::Err<Simple<char>>>(10)
//!     .from_str()
//!     .unwrapped()
//!     .map(Expr::Literal)
//!     .padded();
//!
//! let op = |c| just(c).padded();
//!
//! let expr = atom.pratt((
//!     // We want factorial to happen before any negation, so we need its precedence to be higher than `Expr::Neg`.
//!     postfix(4, op('!'), |lhs| Expr::Factorial(Box::new(lhs))),
//!     // Just like in math, we want that if we write -x^2, our parser parses that as -(x^2), so we need it to have
//!     // exponents bind tighter than our prefix operators.
//!     infix(right(3), op('^'), |l, r| Expr::Pow(Box::new(l), Box::new(r))),
//!     // Notice the conflict with our `Expr::Sub`. This will still parse correctly. We want negation to happen before
//!     // `+` and `-`, so we set its precedence higher.
//!     prefix(2, op('-'), |rhs| Expr::Neg(Box::new(rhs))),
//!     prefix(2, op('*'), |rhs| Expr::Deref(Box::new(rhs))),
//!     // Our `-` and `+` bind the weakest, meaning that even if they occur first in an expression, they will be the
//!     // last executed.
//!     infix(left(1), op('+'), |l, r| Expr::Add(Box::new(l), Box::new(r))),
//!     infix(left(1), op('-'), |l, r| Expr::Sub(Box::new(l), Box::new(r))),
//! ))
//!     .map(|x| x.to_string());
//!
//! assert_eq!(
//!     expr.parse("*1 + -2! - -3^2").into_result(),
//!     Ok("(((*1) + (-(2!))) - (-(3 ^ 2)))".to_string()),
//! );
//! ```

use super::*;

trait Operator<'a, I, O, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    type Op;
    type OpParser: Parser<'a, I, Self::Op, E>;
    const IS_INFIX: bool = false;
    const IS_PREFIX: bool = false;
    const IS_POSTFIX: bool = false;

    fn op_parser(&self) -> &Self::OpParser;
    fn associativity(&self) -> Associativity;
    fn fold_infix(
        &self,
        _lhs: O,
        _op: Self::Op,
        _rhs: O,
        _extra: &mut MapExtra<'a, '_, I, E>,
    ) -> O {
        unreachable!()
    }
    fn fold_prefix(&self, _op: Self::Op, _rhs: O, _extra: &mut MapExtra<'a, '_, I, E>) -> O {
        unreachable!()
    }
    fn fold_postfix(&self, _lhs: O, _op: Self::Op, _extra: &mut MapExtra<'a, '_, I, E>) -> O {
        unreachable!()
    }
}

/// Defines the [associativity](https://en.wikipedia.org/wiki/Associative_property) and binding power of an [`infix`]
/// operator (see [`left`] and [`right`]).
///
/// Higher binding powers should be used for higher precedence operators.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Associativity {
    /// Specifies that the operator should be left-associative, with the given binding power (see [`left`]).
    Left(u16),
    /// Specifies that the operator should be right-associative, with the given binding power (see [`right`]).
    Right(u16),
}

/// Specifies a left [`Associativity`] with the given binding power.
///
/// Left-associative operators are evaluated from the left-most terms, moving rightward. For example, the expression
/// `a + b + c + d` will be evaluated as `((a + b) + c) + d` because addition is conventionally left-associative.
pub fn left(binding_power: u16) -> Associativity {
    Associativity::Left(binding_power)
}

/// Specifies a right [`Associativity`] with the given binding power.
///
/// Right-associative operators are evaluated from the right-most terms, moving leftward. For example, the expression
/// `a ^ b ^ c ^ d` will be evaluated as `a ^ (b ^ (c ^ d))` because exponents are conventionally right-associative.
pub fn right(binding_power: u16) -> Associativity {
    Associativity::Right(binding_power)
}

impl Associativity {
    fn left_power(&self) -> u32 {
        match self {
            Self::Left(x) => *x as u32 * 2,
            Self::Right(x) => *x as u32 * 2 + 1,
        }
    }

    fn right_power(&self) -> u32 {
        match self {
            Self::Left(x) => *x as u32 * 2 + 1,
            Self::Right(x) => *x as u32 * 2,
        }
    }
}

/// See [`infix`].
pub struct Infix<A, F, Op, Args> {
    op_parser: A,
    fold: F,
    associativity: Associativity,
    #[allow(dead_code)]
    phantom: EmptyPhantom<(Op, Args)>,
}

impl<A: Copy, F: Copy, Op, Args> Copy for Infix<A, F, Op, Args> {}
impl<A: Clone, F: Clone, Op, Args> Clone for Infix<A, F, Op, Args> {
    fn clone(&self) -> Self {
        Self {
            op_parser: self.op_parser.clone(),
            fold: self.fold.clone(),
            associativity: self.associativity,
            phantom: EmptyPhantom::new(),
        }
    }
}

/// Specify a binary infix operator for a pratt parser with the given associativity, binding power, and
/// [fold function](crate::pratt#fold-functions).
///
/// Operators like addition, subtraction, multiplication, division, remainder, exponentiation, etc. are infix binary
/// operators in most languages.
///
/// See [`left`] and [`right`] for information about associativity.
///
/// The fold function (the last argument) must have one of the following signatures:
///
/// ```ignore
/// // Combine the left and right operands
/// impl Fn(O, O) -> O
/// // Combine the left operand, the operator itself, and the right operand
/// impl Fn(O, Op, O) -> O
/// // Combine the left operand, the operator itself, the right operand, and a [`MapExtra`] covering the whole operation
/// impl Fn(O, Op, O, &mut MapExtra<'a, '_, I, E>) -> O
/// ```
pub const fn infix<A, F, Op, Args>(
    associativity: Associativity,
    op_parser: A,
    fold: F,
) -> Infix<A, F, Op, Args> {
    Infix {
        op_parser,
        fold,
        associativity,
        phantom: EmptyPhantom::new(),
    }
}

macro_rules! infix_op {
    (|$f:ident : Fn($($Arg:ty),*) -> O, $lhs:ident, $op:ident, $rhs:ident, $extra:ident| $invoke:expr) => {
        impl<'a, I, O, E, A, F, Op> Operator<'a, I, O, E> for Infix<A, F, Op, ($($Arg,)*)>
        where
            I: Input<'a>,
            E: ParserExtra<'a, I>,
            A: Parser<'a, I, Op, E>,
            F: Fn($($Arg),*) -> O,
        {
            type Op = Op;
            type OpParser = A;
            const IS_INFIX: bool = true;
            #[inline(always)] fn op_parser(&self) -> &Self::OpParser { &self.op_parser }
            #[inline(always)] fn associativity(&self) -> Associativity { self.associativity }
            #[inline(always)] fn fold_infix(&self, $lhs: O, $op: Self::Op, $rhs: O, $extra: &mut MapExtra<'a, '_, I, E>) -> O { let $f = &self.fold; $invoke }
        }
    };
}

// Allow `|lhs, rhs| <expr>` to be used as a fold closure for infix operators
infix_op!(|f: Fn(O, O) -> O, lhs, _op, rhs, _extra| f(lhs, rhs));
// Allow `|lhs, op, rhs| <expr>` to be used as a fold closure for infix operators
infix_op!(|f: Fn(O, Op, O) -> O, lhs, op, rhs, _extra| f(lhs, op, rhs));
// Allow `|lhs, op, rhs, extra| <expr>` to be used as a fold closure for infix operators
infix_op!(
    |f: Fn(O, Op, O, &mut MapExtra<'a, '_, I, E>) -> O, lhs, op, rhs, extra| f(lhs, op, rhs, extra)
);

/// See [`prefix`].
pub struct Prefix<A, F, Op, Args> {
    op_parser: A,
    fold: F,
    binding_power: u16,
    #[allow(dead_code)]
    phantom: EmptyPhantom<(Op, Args)>,
}

impl<A: Copy, F: Copy, Op, Args> Copy for Prefix<A, F, Op, Args> {}
impl<A: Clone, F: Clone, Op, Args> Clone for Prefix<A, F, Op, Args> {
    fn clone(&self) -> Self {
        Self {
            op_parser: self.op_parser.clone(),
            fold: self.fold.clone(),
            binding_power: self.binding_power,
            phantom: EmptyPhantom::new(),
        }
    }
}

/// Specify a unary prefix operator for a pratt parser with the given binding power and
/// [fold function](crate::pratt#fold-functions).
///
/// Operators like negation, not, dereferencing, etc. are prefix unary operators in most languages.
///
/// The fold function (the last argument) must have one of the following signatures:
///
/// ```ignore
/// // Transform the operand
/// impl Fn(O) -> O
/// // Combine the operator itself and the operand
/// impl Fn(Op, O) -> O
/// // Combine the operator itself, the operand, and a [`MapExtra`] covering the whole operation
/// impl Fn(Op, O, &mut MapExtra<'a, '_, I, E>) -> O
/// ```
pub const fn prefix<A, F, Op, Args>(
    binding_power: u16,
    op_parser: A,
    fold: F,
) -> Prefix<A, F, Op, Args> {
    Prefix {
        op_parser,
        fold,
        binding_power,
        phantom: EmptyPhantom::new(),
    }
}

macro_rules! prefix_op {
    (|$f:ident : Fn($($Arg:ty),*) -> O, $op:ident, $rhs:ident, $extra:ident| $invoke:expr) => {
        impl<'a, I, O, E, A, F, Op> Operator<'a, I, O, E> for Prefix<A, F, Op, ($($Arg,)*)>
        where
            I: Input<'a>,
            E: ParserExtra<'a, I>,
            A: Parser<'a, I, Op, E>,
            F: Fn($($Arg),*) -> O,
        {
            type Op = Op;
            type OpParser = A;
            const IS_PREFIX: bool = true;
            #[inline(always)] fn op_parser(&self) -> &Self::OpParser { &self.op_parser }
            #[inline(always)] fn associativity(&self) -> Associativity { Associativity::Left(self.binding_power) }
            #[inline(always)] fn fold_prefix(&self, $op: Self::Op, $rhs: O, $extra: &mut MapExtra<'a, '_, I, E>) -> O { let $f = &self.fold; $invoke }
        }
    };
}

// Allow `|rhs| <expr>` to be used as a fold closure for prefix operators
prefix_op!(|f: Fn(O) -> O, _op, rhs, _extra| f(rhs));
// Allow `|op, rhs| <expr>` to be used as a fold closure for prefix operators
prefix_op!(|f: Fn(Op, O) -> O, op, rhs, _extra| f(op, rhs));
// Allow `|op, rhs, span| <expr>` to be used as a fold closure for prefix operators
prefix_op!(|f: Fn(Op, O, &mut MapExtra<'a, '_, I, E>) -> O, op, rhs, extra| f(op, rhs, extra));

/// See [`postfix`].
pub struct Postfix<A, F, Op, Args> {
    op_parser: A,
    fold: F,
    binding_power: u16,
    #[allow(dead_code)]
    phantom: EmptyPhantom<(Op, Args)>,
}

impl<A: Copy, F: Copy, Op, Args> Copy for Postfix<A, F, Op, Args> {}
impl<A: Clone, F: Clone, Op, Args> Clone for Postfix<A, F, Op, Args> {
    fn clone(&self) -> Self {
        Self {
            op_parser: self.op_parser.clone(),
            fold: self.fold.clone(),
            binding_power: self.binding_power,
            phantom: EmptyPhantom::new(),
        }
    }
}

/// Specify a unary postfix operator for a pratt parser with the given binding power and
/// [fold function](crate::pratt#fold-functions).
///
/// Operators like factorial, field access, function composition, etc. are postfix unary operators in most languages.
///
/// The fold function (the last argument) must have one of the following signatures:
///
/// ```ignore
/// // Transform the operand
/// impl Fn(O) -> O
/// // Combine the operand and the operator itself
/// impl Fn(O, Op) -> O
/// // Combine the operand, the operator itself, and a [`MapExtra`] covering the whole operation
/// impl Fn(Op, O, &mut MapExtra<'a, '_, I, E>) -> O
/// ```
pub const fn postfix<A, F, Op, Args>(
    binding_power: u16,
    op_parser: A,
    fold: F,
) -> Postfix<A, F, Op, Args> {
    Postfix {
        op_parser,
        fold,
        binding_power,
        phantom: EmptyPhantom::new(),
    }
}

macro_rules! postfix_op {
    (|$f:ident : Fn($($Arg:ty),*) -> O, $lhs:ident, $op:ident, $extra:ident| $invoke:expr) => {
        impl<'a, I, O, E, A, F, Op> Operator<'a, I, O, E> for Postfix<A, F, Op, ($($Arg,)*)>
        where
            I: Input<'a>,
            E: ParserExtra<'a, I>,
            A: Parser<'a, I, Op, E>,
            F: Fn($($Arg),*) -> O,
        {
            type Op = Op;
            type OpParser = A;
            const IS_POSTFIX: bool = true;
            #[inline(always)] fn op_parser(&self) -> &Self::OpParser { &self.op_parser }
            #[inline(always)] fn associativity(&self) -> Associativity { Associativity::Left(self.binding_power) }
            #[inline(always)] fn fold_postfix(&self, $lhs: O, $op: Self::Op, $extra: &mut MapExtra<'a, '_, I, E>) -> O { let $f = &self.fold; $invoke }
        }
    };
}

// Allow `|lhs| <expr>` to be used as a fold closure for postfix operators
postfix_op!(|f: Fn(O) -> O, lhs, _op, _extra| f(lhs));
// Allow `|lhs, op| <expr>` to be used as a fold closure for postfix operators
postfix_op!(|f: Fn(O, Op) -> O, lhs, op, _extra| f(lhs, op));
// Allow `|lhs, op, span| <expr>` to be used as a fold closure for postfix operators
postfix_op!(|f: Fn(O, Op, &mut MapExtra<'a, '_, I, E>) -> O, lhs, op, extra| f(lhs, op, extra));

/// See [`Parser::pratt`].
#[derive(Copy, Clone)]
pub struct Pratt<Atom, Ops> {
    pub(crate) atom: Atom,
    pub(crate) ops: Ops,
}

macro_rules! impl_pratt_for_tuple {
    () => {};
    ($head:ident $($X:ident)*) => {
        impl_pratt_for_tuple!($($X)*);
        impl_pratt_for_tuple!(~ $head $($X)*);
    };
    (~ $($X:ident)+) => {
        #[allow(unused_variables, non_snake_case)]
        impl<'a, Atom, $($X),*> Pratt<Atom, ($($X,)*)> {
            #[inline]
            fn pratt_go<M: Mode, I, O, E>(&self, inp: &mut InputRef<'a, '_, I, E>, min_power: u32) -> PResult<M, O>
            where
                I: Input<'a>,
                E: ParserExtra<'a, I>,
                Atom: Parser<'a, I, O, E>,
                $($X: Operator<'a, I, O, E>),*
            {
                let pre_expr = inp.save();
                let mut lhs = 'choice: {
                    let ($($X,)*) = &self.ops;

                    // Prefix unary operators
                    $(
                        if $X::IS_PREFIX {
                            match $X.op_parser().go::<M>(inp) {
                                Ok(op) => {
                                    match recursive::recurse(|| self.pratt_go::<M, _, _, _>(inp, $X.associativity().left_power())) {
                                        Ok(rhs) => break 'choice M::combine(op, rhs, |op, rhs| {
                                            $X.fold_prefix(op, rhs, &mut MapExtra::new(pre_expr.offset(), inp))
                                        }),
                                        Err(()) => inp.rewind(pre_expr),
                                    }
                                },
                                Err(()) => inp.rewind(pre_expr),
                            }
                        }
                    )*

                    self.atom.go::<M>(inp)?
                };

                loop {
                    let ($($X,)*) = &self.ops;

                    let pre_op = inp.save();

                    // Postfix unary operators
                    $(
                        let assoc = $X.associativity();
                        if $X::IS_POSTFIX && assoc.right_power() >= min_power {
                            match $X.op_parser().go::<M>(inp) {
                                Ok(op) => {
                                    lhs = M::combine(lhs, op, |lhs, op| {
                                        $X.fold_postfix(lhs, op, &mut MapExtra::new(pre_expr.offset(), inp))
                                    });
                                    continue
                                },
                                Err(()) => inp.rewind(pre_op),
                            }
                        }
                    )*

                    // Infix binary operators
                    $(
                        let assoc = $X.associativity();
                        if $X::IS_INFIX && assoc.left_power() >= min_power {
                            match $X.op_parser().go::<M>(inp) {
                                Ok(op) => match recursive::recurse(|| self.pratt_go::<M, _, _, _>(inp, assoc.right_power())) {
                                    Ok(rhs) => {
                                        lhs = M::combine(
                                            M::combine(lhs, rhs, |lhs, rhs| (lhs, rhs)),
                                            op,
                                            |(lhs, rhs), op| {
                                                $X.fold_infix(lhs, op, rhs, &mut MapExtra::new(pre_expr.offset(), inp))
                                            },
                                        );
                                        continue
                                    },
                                    Err(()) => inp.rewind(pre_op),
                                },
                                Err(()) => inp.rewind(pre_op),
                            }
                        }
                    )*

                    inp.rewind(pre_op);
                    break;
                }

                Ok(lhs)
            }
        }

        #[allow(unused_variables, non_snake_case)]
        impl<'a, I, O, E, Atom, $($X),*> ParserSealed<'a, I, O, E> for Pratt<Atom, ($($X,)*)>
        where
            I: Input<'a>,
            E: ParserExtra<'a, I>,
            Atom: Parser<'a, I, O, E>,
            $($X: Operator<'a, I, O, E>),*
        {
            fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
                self.pratt_go::<M, _, _, _>(inp, 0)
            }

            go_extra!(O);
        }
    };
}

impl_pratt_for_tuple!(
    AA_ AB_ AC_ AD_ AE_ AF_ AG_ AH_ AI_ AJ_ AK_ AL_ AM_ AN_ AO_ AP_ AQ_ AR_ AS_ AT_ AU_ AV_ AW_ AX_ AY_ AZ_
    BA_ BB_ BC_ BD_ BE_ BF_ BG_ BH_ BI_ BJ_ BK_ BL_ BM_ BN_ BO_ BP_ BQ_ BR_ BS_ BT_ BU_ BV_ BW_ BX_ BY_ BZ_
    CA_ CB_ CC_ CD_ CE_ CF_ CG_ CH_ CI_ CJ_ CK_ CL_ CM_ CN_ CO_ CP_ CQ_ CR_ CS_ CT_ CU_ CV_ CW_ CX_ CY_ CZ_
    DA_ DB_ DC_ DD_ DE_ DF_ DG_ DH_ DI_ DJ_ DK_ DL_ DM_ DN_ DO_ DP_ DQ_ DR_ DS_ DT_ DU_ DV_ DW_ DX_ DY_ DZ_
    EA_ EB_ EC_ ED_ EE_ EF_ EG_ EH_ EI_ EJ_ EK_ EL_ EM_ EN_ EO_ EP_ EQ_ ER_ ES_ ET_ EU_ EV_ EW_ EX_ EY_ EZ_
    FA_ FB_ FC_ FD_ FE_ FF_ FG_ FH_ FI_ FJ_ FK_ FL_ FM_ FN_ FO_ FP_ FQ_ FR_ FS_ FT_ FU_ FV_ FW_ FX_ FY_ FZ_
    GA_ GB_ GC_ GD_ GE_ GF_ GG_ GH_ GI_ GJ_ GK_ GL_ GM_ GN_ GO_ GP_ GQ_ GR_ GS_ GT_ GU_ GV_ GW_ GX_ GY_ GZ_
    HA_ HB_ HC_ HD_ HE_ HF_ HG_ HH_ HI_ HJ_ HK_ HL_ HM_ HN_ HO_ HP_ HQ_ HR_ HS_ HT_ HU_ HV_ HW_ HX_ HY_ HZ_
    IA_ IB_ IC_ ID_ IE_ IF_ IG_ IH_ II_ IJ_ IK_ IL_ IM_ IN_ IO_ IP_ IQ_ IR_ IS_ IT_ IU_ IV_ IW_ IX_ IY_ IZ_
    JA_ JB_ JC_ JD_ JE_ JF_ JG_ JH_ JI_ JJ_ JK_ JL_ JM_ JN_ JO_ JP_ JQ_ JR_ JS_ JT_ JU_ JV_ JW_ JX_ JY_ JZ_
    KA_ KB_ KC_ KD_ KE_ KF_ KG_ KH_ KI_ KJ_ KK_ KL_ KM_ KN_ KO_ KP_ KQ_ KR_ KS_ KT_ KU_ KV_ KW_ KX_ KY_ KZ_
    LA_ LB_ LC_ LD_ LE_ LF_ LG_ LH_ LI_ LJ_ LK_ LL_ LM_ LN_ LO_ LP_ LQ_ LR_ LS_ LT_ LU_ LV_ LW_ LX_ LY_ LZ_
    MA_ MB_ MC_ MD_ ME_ MF_ MG_ MH_ MI_ MJ_ MK_ ML_ MM_ MN_ MO_ MP_ MQ_ MR_ MS_ MT_ MU_ MV_ MW_ MX_ MY_ MZ_
    NA_ NB_ NC_ ND_ NE_ NF_ NG_ NH_ NI_ NJ_ NK_ NL_ NM_ NN_ NO_ NP_ NQ_ NR_ NS_ NT_ NU_ NV_ NW_ NX_ NY_ NZ_
    OA_ OB_ OC_ OD_ OE_ OF_ OG_ OH_ OI_ OJ_ OK_ OL_ OM_ ON_ OO_ OP_ OQ_ OR_ OS_ OT_ OU_ OV_ OW_ OX_ OY_ OZ_
    PA_ PB_ PC_ PD_ PE_ PF_ PG_ PH_ PI_ PJ_ PK_ PL_ PM_ PN_ PO_ PP_ PQ_ PR_ PS_ PT_ PU_ PV_ PW_ PX_ PY_ PZ_
    QA_ QB_ QC_ QD_ QE_ QF_ QG_ QH_ QI_ QJ_ QK_ QL_ QM_ QN_ QO_ QP_ QQ_ QR_ QS_ QT_ QU_ QV_ QW_ QX_ QY_ QZ_
    RA_ RB_ RC_ RD_ RE_ RF_ RG_ RH_ RI_ RJ_ RK_ RL_ RM_ RN_ RO_ RP_ RQ_ RR_ RS_ RT_ RU_ RV_ RW_ RX_ RY_ RZ_
    SA_ SB_ SC_ SD_ SE_ SF_ SG_ SH_ SI_ SJ_ SK_ SL_ SM_ SN_ SO_ SP_ SQ_ SR_ SS_ ST_ SU_ SV_ SW_ SX_ SY_ SZ_
    TA_ TB_ TC_ TD_ TE_ TF_ TG_ TH_ TI_ TJ_ TK_ TL_ TM_ TN_ TO_ TP_ TQ_ TR_ TS_ TT_ TU_ TV_ TW_ TX_ TY_ TZ_
    UA_ UB_ UC_ UD_ UE_ UF_ UG_ UH_ UI_ UJ_ UK_ UL_ UM_ UN_ UO_ UP_ UQ_ UR_ US_ UT_ UU_ UV_ UW_ UX_ UY_ UZ_
    VA_ VB_ VC_ VD_ VE_ VF_ VG_ VH_ VI_ VJ_ VK_ VL_ VM_ VN_ VO_ VP_ VQ_ VR_ VS_ VT_ VU_ VV_ VW_ VX_ VY_ VZ_
    WA_ WB_ WC_ WD_ WE_ WF_ WG_ WH_ WI_ WJ_ WK_ WL_ WM_ WN_ WO_ WP_ WQ_ WR_ WS_ WT_ WU_ WV_ WW_ WX_ WY_ WZ_
    XA_ XB_ XC_ XD_ XE_ XF_ XG_ XH_ XI_ XJ_ XK_ XL_ XM_ XN_ XO_ XP_ XQ_ XR_ XS_ XT_ XU_ XV_ XW_ XX_ XY_ XZ_
    YA_ YB_ YC_ YD_ YE_ YF_ YG_ YH_ YI_ YJ_ YK_ YL_ YM_ YN_ YO_ YP_ YQ_ YR_ YS_ YT_ YU_ YV_ YW_ YX_ YY_ YZ_
    ZA_ ZB_ ZC_ ZD_ ZE_ ZF_ ZG_ ZH_ ZI_ ZJ_ ZK_ ZL_ ZM_ ZN_ ZO_ ZP_ ZQ_ ZR_ ZS_ ZT_ ZU_ ZV_ ZW_ ZX_ ZY_ ZZ_
);

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

    fn parser<'a>() -> impl Parser<'a, &'a str, i64> {
        let atom = text::int(10).padded().from_str::<i64>().unwrapped();

        atom.pratt((
            prefix(2, just('-'), |x: i64| -x),
            postfix(2, just('!'), factorial),
            infix(left(0), just('+'), |l, r| l + r),
            infix(left(0), just('-'), |l, r| l - r),
            infix(left(1), just('*'), |l, r| l * r),
            infix(left(1), just('/'), |l, _, r| l / r),
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

    // TODO: Make this work
    // fn parser_dynamic<'a>() -> impl Parser<'a, &'a str, i64> {
    //     let atom = text::int(10).padded().from_str::<i64>().unwrapped();

    //     atom.pratt(vec![
    //         prefix(2, just('-'), |x: i64| -x).into(),
    //         postfix(2, just('!'), factorial).into(),
    //         infix(left(0), just('+'), |l, r| l + r).into(),
    //         infix(left(0), just('-'), |l, r| l - r).into(),
    //         infix(left(1), just('*'), |l, r| l * r).into(),
    //         infix(left(1), just('/'), |l, _, r| l / r).into(),
    //     ])
    // }

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

    fn u(e: fn(Box<Expr>) -> Expr, r: Expr) -> Expr {
        e(Box::new(r))
    }
    fn i(e: fn(Box<Expr>, Box<Expr>) -> Expr, l: Expr, r: Expr) -> Expr {
        e(Box::new(l), Box::new(r))
    }

    fn expr_parser<'a>() -> impl Parser<'a, &'a str, String, Err<Simple<'a, char>>> {
        let atom = text::int(10).from_str().unwrapped().map(Expr::Literal);

        atom.pratt((
            infix(left(0), just('+'), |l, r| i(Expr::Add, l, r)),
            infix(left(0), just('-'), |l, r| i(Expr::Sub, l, r)),
            infix(right(1), just('*'), |l, r| i(Expr::Mul, l, r)),
            infix(right(1), just('/'), |l, r| i(Expr::Div, l, r)),
        ))
        .map(|x| x.to_string())
    }

    fn complete_parser<'a>() -> impl Parser<'a, &'a str, String, Err<Simple<'a, char>>> {
        expr_parser().then_ignore(end())
    }

    fn parse(input: &str) -> ParseResult<String, Simple<char>> {
        complete_parser().parse(input)
    }

    fn parse_partial(input: &str) -> ParseResult<String, Simple<char>> {
        expr_parser().lazy().parse(input)
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

        let parser = atom
            .pratt((
                // -- Prefix
                // Because we defined '*' and '/' as right associative operators,
                // in order to get these to function as expected, their strength
                // must be higher
                prefix(2, just('-'), |r| u(Expr::Negate, r)),
                prefix(2, just('~'), |r| u(Expr::Not, r)),
                // This is what happens when not
                prefix(1, just('§'), |r| u(Expr::Confusion, r)),
                // -- Infix
                infix(left(0), just('+'), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just('-'), |l, r| i(Expr::Sub, l, r)),
                infix(right(1), just('*'), |l, r| i(Expr::Mul, l, r)),
                infix(right(1), just('/'), |l, r| i(Expr::Div, l, r)),
            ))
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

        let parser = atom
            .pratt((
                // -- Postfix
                // Because we defined '*' and '/' as right associative operators,
                // in order to get these to function as expected, their strength
                // must be higher
                postfix(2, just('!'), |l| u(Expr::Factorial, l)),
                // This is what happens when not
                postfix(0, just('$'), |l| u(Expr::Value, l)),
                // -- Infix
                infix(left(1), just('+'), |l, r| i(Expr::Add, l, r)),
                infix(left(1), just('-'), |l, r| i(Expr::Sub, l, r)),
                infix(right(2), just('*'), |l, r| i(Expr::Mul, l, r)),
                infix(right(2), just('/'), |l, r| i(Expr::Div, l, r)),
            ))
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

        let parser = atom
            .pratt((
                // -- Prefix
                prefix(4, just('-'), |r| u(Expr::Negate, r)),
                prefix(4, just('~'), |r| u(Expr::Not, r)),
                prefix(1, just('§'), |r| u(Expr::Confusion, r)),
                // -- Postfix
                postfix(5, just('!'), |l| u(Expr::Factorial, l)),
                postfix(0, just('$'), |l| u(Expr::Value, l)),
                // -- Infix
                infix(left(1), just('+'), |l, r| i(Expr::Add, l, r)),
                infix(left(1), just('-'), |l, r| i(Expr::Sub, l, r)),
                infix(right(2), just('*'), |l, r| i(Expr::Mul, l, r)),
                infix(right(2), just('/'), |l, r| i(Expr::Div, l, r)),
            ))
            .map(|x| x.to_string());
        assert_eq!(
            parser.parse("§1+-~2!$*3").into_result(),
            Ok("(((§(1 + (-(~(2!)))))$) * 3)".to_string()),
        )
    }

    #[test]
    fn with_lots_of_ops() {
        let atom = text::int::<_, _, Err<Simple<char>>>(10)
            .from_str()
            .unwrapped()
            .map(Expr::Literal);

        let parser = atom
            .pratt((
                infix(left(0), just("AA"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("AB"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("AC"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("AD"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("AE"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("AF"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("AG"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("AH"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("AI"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("AJ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("AK"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("AL"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("AM"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("AN"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("AO"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("AP"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("AQ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("AR"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("AS"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("AT"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("AU"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("AV"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("AW"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("AX"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("AY"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("AZ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("BA"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("BB"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("BC"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("BD"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("BE"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("BF"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("BG"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("BH"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("BI"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("BJ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("BK"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("BL"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("BM"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("BN"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("BO"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("BP"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("BQ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("BR"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("BS"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("BT"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("BU"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("BV"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("BW"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("BX"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("BY"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("BZ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("CA"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("CB"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("CC"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("CD"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("CE"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("CF"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("CG"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("CH"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("CI"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("CJ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("CK"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("CL"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("CM"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("CN"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("CO"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("CP"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("CQ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("CR"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("CS"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("CT"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("CU"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("CV"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("CW"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("CX"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("CY"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("CZ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("DA"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("DB"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("DC"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("DD"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("DE"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("DF"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("DG"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("DH"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("DI"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("DJ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("DK"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("DL"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("DM"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("DN"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("DO"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("DP"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("DQ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("DR"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("DS"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("DT"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("DU"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("DV"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("DW"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("DX"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("DY"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("DZ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("EA"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("EB"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("EC"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ED"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("EE"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("EF"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("EG"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("EH"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("EI"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("EJ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("EK"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("EL"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("EM"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("EN"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("EO"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("EP"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("EQ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ER"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ES"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ET"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("EU"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("EV"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("EW"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("EX"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("EY"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("EZ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("FA"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("FB"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("FC"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("FD"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("FE"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("FF"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("FG"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("FH"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("FI"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("FJ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("FK"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("FL"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("FM"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("FN"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("FO"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("FP"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("FQ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("FR"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("FS"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("FT"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("FU"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("FV"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("FW"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("FX"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("FY"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("FZ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("GA"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("GB"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("GC"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("GD"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("GE"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("GF"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("GG"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("GH"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("GI"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("GJ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("GK"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("GL"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("GM"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("GN"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("GO"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("GP"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("GQ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("GR"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("GS"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("GT"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("GU"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("GV"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("GW"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("GX"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("GY"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("GZ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("HA"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("HB"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("HC"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("HD"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("HE"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("HF"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("HG"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("HH"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("HI"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("HJ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("HK"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("HL"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("HM"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("HN"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("HO"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("HP"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("HQ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("HR"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("HS"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("HT"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("HU"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("HV"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("HW"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("HX"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("HY"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("HZ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("IA"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("IB"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("IC"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ID"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("IE"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("IF"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("IG"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("IH"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("II"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("IJ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("IK"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("IL"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("IM"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("IN"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("IO"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("IP"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("IQ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("IR"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("IS"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("IT"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("IU"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("IV"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("IW"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("IX"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("IY"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("IZ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("JA"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("JB"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("JC"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("JD"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("JE"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("JF"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("JG"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("JH"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("JI"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("JJ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("JK"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("JL"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("JM"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("JN"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("JO"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("JP"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("JQ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("JR"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("JS"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("JT"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("JU"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("JV"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("JW"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("JX"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("JY"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("JZ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("KA"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("KB"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("KC"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("KD"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("KE"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("KF"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("KG"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("KH"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("KI"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("KJ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("KK"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("KL"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("KM"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("KN"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("KO"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("KP"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("KQ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("KR"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("KS"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("KT"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("KU"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("KV"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("KW"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("KX"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("KY"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("KZ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("LA"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("LB"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("LC"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("LD"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("LE"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("LF"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("LG"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("LH"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("LI"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("LJ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("LK"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("LL"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("LM"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("LN"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("LO"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("LP"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("LQ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("LR"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("LS"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("LT"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("LU"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("LV"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("LW"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("LX"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("LY"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("LZ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("MA"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("MB"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("MC"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("MD"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ME"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("MF"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("MG"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("MH"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("MI"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("MJ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("MK"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ML"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("MM"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("MN"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("MO"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("MP"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("MQ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("MR"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("MS"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("MT"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("MU"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("MV"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("MW"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("MX"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("MY"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("MZ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("NA"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("NB"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("NC"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ND"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("NE"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("NF"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("NG"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("NH"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("NI"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("NJ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("NK"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("NL"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("NM"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("NN"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("NO"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("NP"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("NQ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("NR"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("NS"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("NT"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("NU"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("NV"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("NW"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("NX"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("NY"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("NZ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("OA"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("OB"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("OC"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("OD"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("OE"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("OF"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("OG"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("OH"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("OI"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("OJ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("OK"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("OL"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("OM"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ON"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("OO"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("OP"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("OQ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("OR"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("OS"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("OT"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("OU"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("OV"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("OW"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("OX"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("OY"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("OZ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("PA"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("PB"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("PC"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("PD"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("PE"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("PF"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("PG"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("PH"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("PI"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("PJ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("PK"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("PL"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("PM"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("PN"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("PO"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("PP"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("PQ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("PR"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("PS"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("PT"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("PU"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("PV"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("PW"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("PX"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("PY"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("PZ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("QA"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("QB"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("QC"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("QD"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("QE"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("QF"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("QG"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("QH"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("QI"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("QJ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("QK"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("QL"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("QM"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("QN"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("QO"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("QP"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("QQ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("QR"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("QS"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("QT"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("QU"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("QV"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("QW"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("QX"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("QY"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("QZ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("RA"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("RB"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("RC"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("RD"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("RE"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("RF"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("RG"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("RH"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("RI"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("RJ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("RK"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("RL"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("RM"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("RN"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("RO"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("RP"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("RQ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("RR"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("RS"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("RT"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("RU"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("RV"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("RW"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("RX"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("RY"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("RZ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("SA"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("SB"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("SC"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("SD"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("SE"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("SF"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("SG"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("SH"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("SI"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("SJ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("SK"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("SL"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("SM"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("SN"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("SO"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("SP"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("SQ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("SR"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("SS"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ST"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("SU"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("SV"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("SW"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("SX"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("SY"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("SZ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("TA"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("TB"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("TC"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("TD"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("TE"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("TF"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("TG"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("TH"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("TI"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("TJ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("TK"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("TL"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("TM"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("TN"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("TO"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("TP"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("TQ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("TR"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("TS"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("TT"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("TU"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("TV"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("TW"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("TX"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("TY"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("TZ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("UA"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("UB"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("UC"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("UD"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("UE"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("UF"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("UG"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("UH"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("UI"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("UJ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("UK"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("UL"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("UM"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("UN"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("UO"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("UP"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("UQ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("UR"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("US"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("UT"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("UU"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("UV"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("UW"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("UX"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("UY"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("UZ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("VA"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("VB"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("VC"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("VD"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("VE"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("VF"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("VG"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("VH"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("VI"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("VJ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("VK"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("VL"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("VM"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("VN"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("VO"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("VP"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("VQ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("VR"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("VS"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("VT"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("VU"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("VV"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("VW"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("VX"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("VY"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("VZ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("WA"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("WB"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("WC"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("WD"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("WE"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("WF"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("WG"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("WH"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("WI"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("WJ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("WK"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("WL"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("WM"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("WN"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("WO"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("WP"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("WQ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("WR"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("WS"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("WT"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("WU"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("WV"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("WW"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("WX"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("WY"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("WZ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("XA"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("XB"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("XC"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("XD"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("XE"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("XF"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("XG"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("XH"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("XI"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("XJ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("XK"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("XL"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("XM"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("XN"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("XO"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("XP"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("XQ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("XR"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("XS"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("XT"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("XU"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("XV"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("XW"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("XX"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("XY"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("XZ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("YA"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("YB"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("YC"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("YD"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("YE"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("YF"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("YG"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("YH"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("YI"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("YJ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("YK"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("YL"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("YM"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("YN"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("YO"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("YP"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("YQ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("YR"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("YS"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("YT"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("YU"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("YV"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("YW"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("YX"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("YY"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("YZ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ZA"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ZB"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ZC"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ZD"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ZE"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ZF"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ZG"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ZH"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ZI"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ZJ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ZK"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ZL"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ZM"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ZN"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ZO"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ZP"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ZQ"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ZR"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ZS"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ZT"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ZU"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ZV"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ZW"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ZX"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ZY"), |l, r| i(Expr::Add, l, r)),
                infix(left(0), just("ZZ"), |l, r| i(Expr::Add, l, r)),
            ))
            .map(|x| x.to_string());
        assert_eq!(
            parser.parse("1AA2BB3CC4WW5XX6ZZ7").into_result(),
            Ok("1 + 2 + 3 + 4 + 5 + 6 + 7".to_string()),
        )
    }
}
