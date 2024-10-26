//! A small module that implements the [`Parser`] trait for the
//! [`either::Either`](https://docs.rs/either/latest/either/enum.Either.html) type.

use super::*;
use ::either::Either;

impl<'src, L, R, I, O, E> Parser<'src, I, O, E> for Either<L, R>
where
    I: Input<'src>,
    E: ParserExtra<'src, I>,
    L: Parser<'src, I, O, E>,
    R: Parser<'src, I, O, E>,
{
    fn go<M: crate::private::Mode>(
        &self,
        inp: &mut crate::input::InputRef<'src, '_, I, E>,
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

#[cfg(test)]
mod tests {
    use crate::{
        prelude::{any, just},
        IterParser, Parser,
    };
    use either::Either;

    fn parser<'src>() -> impl Parser<'src, &'src str, Vec<u64>> {
        any()
            .filter(|c: &char| c.is_ascii_digit())
            .repeated()
            .at_least(1)
            .at_most(3)
            .to_slice()
            .map(|b: &str| b.parse::<u64>().unwrap())
            .padded()
            .separated_by(just(',').padded())
            .allow_trailing()
            .collect()
            .delimited_by(just('['), just(']'))
    }

    #[test]
    fn either() {
        let parsers = [Either::Left(parser()), Either::Right(parser())];
        for parser in parsers {
            assert_eq!(
                parser.parse("[122 , 23,43,    4, ]").into_result(),
                Ok(vec![122, 23, 43, 4]),
            );
            assert_eq!(
                parser.parse("[0, 3, 6, 900,120]").into_result(),
                Ok(vec![0, 3, 6, 900, 120]),
            );
            assert_eq!(
                parser.parse("[200,400,50  ,0,0, ]").into_result(),
                Ok(vec![200, 400, 50, 0, 0]),
            );

            assert!(parser.parse("[1234,123,12,1]").has_errors());
            assert!(parser.parse("[,0, 1, 456]").has_errors());
            assert!(parser.parse("[3, 4, 5, 67 89,]").has_errors());
        }
    }
}
