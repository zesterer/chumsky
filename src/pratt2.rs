#![allow(missing_docs)]

use super::*;

trait Operator<'a, I, O, E>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
{
    type Op;
    type OpParser: Parser<'a, I, Self::Op, E>;
    const INFIX: bool = false;
    const PREFIX: bool = false;
    const POSTFIX: bool = false;

    fn op_parser(&self) -> &Self::OpParser;
    fn associativity(&self) -> Associativity;
    fn fold_infix(&self, lhs: O, op: Self::Op, rhs: O, span: I::Span) -> O {
        unreachable!()
    }
    fn fold_prefix(&self, op: Self::Op, rhs: O, span: I::Span) -> O {
        unreachable!()
    }
    fn fold_postfix(&self, lhs: O, op: Self::Op, span: I::Span) -> O {
        unreachable!()
    }
}

#[derive(Copy, Clone, PartialEq)]
pub enum Associativity {
    Left(u16),
    Right(u16),
}

impl Associativity {
    fn left_power(&self) -> u16 {
        match self {
            Self::Left(x) => x * 2,
            Self::Right(x) => x * 2 + 1,
        }
    }

    fn right_power(&self) -> u16 {
        match self {
            Self::Left(x) => x * 2 + 1,
            Self::Right(x) => x * 2,
        }
    }
}

pub struct Infix<A, F, Op, Args> {
    op_parser: A,
    f: F,
    associativity: Associativity,
    #[allow(dead_code)]
    phantom: EmptyPhantom<(Op, Args)>,
}

pub fn left(binding_power: u16) -> Associativity {
    Associativity::Left(binding_power)
}
pub fn right(binding_power: u16) -> Associativity {
    Associativity::Right(binding_power)
}

pub const fn binary<A, F, Op, Args>(
    associativity: Associativity,
    op_parser: A,
    f: F,
) -> Infix<A, F, Op, Args> {
    Infix {
        op_parser,
        f,
        associativity,
        phantom: EmptyPhantom::new(),
    }
}

impl<'a, I, O, E, A, F, Op> Operator<'a, I, O, E> for Infix<A, F, Op, (O, O)>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, Op, E>,
    F: Fn(O, O) -> O,
{
    type Op = Op;
    type OpParser = A;
    const INFIX: bool = true;

    fn op_parser(&self) -> &Self::OpParser {
        &self.op_parser
    }
    fn associativity(&self) -> Associativity {
        self.associativity
    }
    fn fold_infix(&self, lhs: O, _op: Self::Op, rhs: O, _span: I::Span) -> O {
        (self.f)(lhs, rhs)
    }
}

impl<'a, I, O, E, A, F, Op> Operator<'a, I, O, E> for Infix<A, F, Op, (O, Op, O)>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, Op, E>,
    F: Fn(O, Op, O) -> O,
{
    type Op = Op;
    type OpParser = A;
    const INFIX: bool = true;

    fn op_parser(&self) -> &Self::OpParser {
        &self.op_parser
    }
    fn associativity(&self) -> Associativity {
        self.associativity
    }
    fn fold_infix(&self, lhs: O, op: Self::Op, rhs: O, _span: I::Span) -> O {
        (self.f)(lhs, op, rhs)
    }
}

impl<'a, I, O, E, A, F, Op> Operator<'a, I, O, E> for Infix<A, F, Op, (O, Op, O, I::Span)>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, Op, E>,
    F: Fn(O, Op, O, I::Span) -> O,
{
    type Op = Op;
    type OpParser = A;
    const INFIX: bool = true;

    fn op_parser(&self) -> &Self::OpParser {
        &self.op_parser
    }
    fn associativity(&self) -> Associativity {
        self.associativity
    }
    fn fold_infix(&self, lhs: O, op: Self::Op, rhs: O, span: I::Span) -> O {
        (self.f)(lhs, op, rhs, span)
    }
}

pub struct Prefix<A, F, Op, Args> {
    op_parser: A,
    f: F,
    binding_power: u16,
    #[allow(dead_code)]
    phantom: EmptyPhantom<(Op, Args)>,
}

pub const fn prefix<A, F, Op, Args>(
    binding_power: u16,
    op_parser: A,
    f: F,
) -> Prefix<A, F, Op, Args> {
    Prefix {
        op_parser,
        f,
        binding_power,
        phantom: EmptyPhantom::new(),
    }
}

impl<'a, I, O, E, A, F, Op> Operator<'a, I, O, E> for Prefix<A, F, Op, (O,)>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, Op, E>,
    F: Fn(O) -> O,
{
    type Op = Op;
    type OpParser = A;
    const PREFIX: bool = true;

    fn op_parser(&self) -> &Self::OpParser {
        &self.op_parser
    }
    fn associativity(&self) -> Associativity {
        Associativity::Left(self.binding_power)
    }
    fn fold_prefix(&self, _op: Self::Op, rhs: O, _span: I::Span) -> O {
        (self.f)(rhs)
    }
}

impl<'a, I, O, E, A, F, Op> Operator<'a, I, O, E> for Prefix<A, F, Op, (Op, O)>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, Op, E>,
    F: Fn(Op, O) -> O,
{
    type Op = Op;
    type OpParser = A;
    const PREFIX: bool = true;

    fn op_parser(&self) -> &Self::OpParser {
        &self.op_parser
    }
    fn associativity(&self) -> Associativity {
        Associativity::Left(self.binding_power)
    }
    fn fold_prefix(&self, op: Self::Op, rhs: O, _span: I::Span) -> O {
        (self.f)(op, rhs)
    }
}

impl<'a, I, O, E, A, F, Op> Operator<'a, I, O, E> for Prefix<A, F, Op, (Op, O, I::Span)>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, Op, E>,
    F: Fn(Op, O, I::Span) -> O,
{
    type Op = Op;
    type OpParser = A;
    const PREFIX: bool = true;

    fn op_parser(&self) -> &Self::OpParser {
        &self.op_parser
    }
    fn associativity(&self) -> Associativity {
        Associativity::Left(self.binding_power)
    }
    fn fold_prefix(&self, op: Self::Op, rhs: O, span: I::Span) -> O {
        (self.f)(op, rhs, span)
    }
}

pub struct Postfix<A, F, Op, Args> {
    op_parser: A,
    f: F,
    binding_power: u16,
    #[allow(dead_code)]
    phantom: EmptyPhantom<(Op, Args)>,
}

pub const fn postfix<A, F, Op, Args>(
    binding_power: u16,
    op_parser: A,
    f: F,
) -> Postfix<A, F, Op, Args> {
    Postfix {
        op_parser,
        f,
        binding_power,
        phantom: EmptyPhantom::new(),
    }
}

impl<'a, I, O, E, A, F, Op> Operator<'a, I, O, E> for Postfix<A, F, Op, (O,)>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, Op, E>,
    F: Fn(O) -> O,
{
    type Op = Op;
    type OpParser = A;
    const POSTFIX: bool = true;

    fn op_parser(&self) -> &Self::OpParser {
        &self.op_parser
    }
    fn associativity(&self) -> Associativity {
        Associativity::Left(self.binding_power)
    }
    fn fold_postfix(&self, lhs: O, _op: Self::Op, _span: I::Span) -> O {
        (self.f)(lhs)
    }
}

impl<'a, I, O, E, A, F, Op> Operator<'a, I, O, E> for Postfix<A, F, Op, (Op, O)>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, Op, E>,
    F: Fn(O, Op) -> O,
{
    type Op = Op;
    type OpParser = A;
    const POSTFIX: bool = true;

    fn op_parser(&self) -> &Self::OpParser {
        &self.op_parser
    }
    fn associativity(&self) -> Associativity {
        Associativity::Left(self.binding_power)
    }
    fn fold_postfix(&self, lhs: O, op: Self::Op, _span: I::Span) -> O {
        (self.f)(lhs, op)
    }
}

impl<'a, I, O, E, A, F, Op> Operator<'a, I, O, E> for Postfix<A, F, Op, (Op, O, I::Span)>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, Op, E>,
    F: Fn(O, Op, I::Span) -> O,
{
    type Op = Op;
    type OpParser = A;
    const POSTFIX: bool = true;

    fn op_parser(&self) -> &Self::OpParser {
        &self.op_parser
    }
    fn associativity(&self) -> Associativity {
        Associativity::Left(self.binding_power)
    }
    fn fold_postfix(&self, lhs: O, op: Self::Op, span: I::Span) -> O {
        (self.f)(lhs, op, span)
    }
}

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
            fn pratt_go<M: Mode, I, O, E>(&self, inp: &mut InputRef<'a, '_, I, E>, min_power: u16) -> PResult<M, O>
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
                        if $X::PREFIX {
                            match $X.op_parser().go::<M>(inp) {
                                Ok(op) => {
                                    match self.pratt_go::<M, _, _, _>(inp, $X.associativity().left_power()) {
                                        Ok(rhs) => break 'choice M::combine(op, rhs, |op, rhs| {
                                            let span = inp.span_since(pre_expr.offset());
                                            $X.fold_prefix(op, rhs, span)
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
                        if $X::POSTFIX && assoc.right_power() >= min_power {
                            match $X.op_parser().go::<M>(inp) {
                                Ok(op) => {
                                    lhs = M::combine(lhs, op, |lhs, op| {
                                        let span = inp.span_since(pre_expr.offset());
                                        $X.fold_postfix(lhs, op, span)
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
                        if $X::INFIX && assoc.left_power() >= min_power {
                            match $X.op_parser().go::<M>(inp) {
                                Ok(op) => match self.pratt_go::<M, _, _, _>(inp, assoc.right_power()) {
                                    Ok(rhs) => {
                                        lhs = M::combine(
                                            M::combine(lhs, rhs, |lhs, rhs| (lhs, rhs)),
                                            op,
                                            |(lhs, rhs), op| {
                                                let span = inp.span_since(pre_expr.offset());
                                                $X.fold_infix(lhs, op, rhs, span)
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

impl_pratt_for_tuple!(A_ B_ C_ D_ E_ F_ G_ H_ I_ J_ K_ L_ M_ N_ O_ P_ Q_ R_ S_ T_ U_ V_ W_ X_ Y_ Z_);

#[cfg(test)]
mod tests {
    use super::*;

    fn factorial(x: i64) -> i64 {
        if x == 0 {
            1
        } else {
            x * factorial(x - 1)
        }
    }

    fn parser<'a>() -> impl Parser<'a, &'a str, i64> {
        let atom = text::int(10).padded().from_str::<i64>().unwrapped();

        atom.pratt2((
            prefix(2, just('-'), |_, x: i64| -x),
            postfix(2, just('!'), factorial),
            binary(left(0), just('+'), |l, r| l + r),
            binary(left(0), just('-'), |l, r| l - r),
            binary(left(1), just('*'), |l, r| l * r),
            binary(left(1), just('/'), |l, _, r| l / r),
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
}
