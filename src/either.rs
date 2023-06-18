//! A small module that implements the [`Parser`](Parser) trait for the
//! [`either::Either`](https://docs.rs/either/latest/either/enum.Either.html) type.

use either::Either;

use crate::{
    extra::ParserExtra, prelude::Input, private::ParserSealed, Check, Emit, InputRef, PResult,
    Parser,
};

impl<'a, L, R, I, O, E> ParserSealed<'a, I, O, E> for Either<L, R>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    L: Parser<'a, I, O, E>,
    R: Parser<'a, I, O, E>,
{
    fn go<M: crate::private::Mode>(
        &self,
        inp: &mut crate::input::InputRef<'a, '_, I, E>,
    ) -> crate::private::PResult<M, O>
    where
        Self: Sized,
    {
        match self {
            Either::Left(l) => L::go::<M>(l, inp),
            Either::Right(r) => R::go::<M>(r, inp),
        }
    }

    go_extra!(O);
}
