use chumsky::{
    extension::v1::{Ext, ExtParser},
    input::{InputRef, ValueInput},
    prelude::*,
};

use crate::char::Char;

pub trait ParserExt<'a, I, O, E>: Parser<'a, I, O, E>
where
    I: Input<'a>,
    E: extra::ParserExtra<'a, I>,
{
    /// Parse a pattern, ignoring any amount of whitespace both before and after the pattern.
    ///
    /// The output type of this parser is `O`, the same as the original parser.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// # use chumsky_text::prelude::*;
    /// let ident = text::ascii::ident::<_, _, extra::Err<Simple<char>>>().padded();
    ///
    /// // A pattern with no whitespace surrounding it is accepted
    /// assert_eq!(ident.parse("hello").into_result(), Ok("hello"));
    /// // A pattern with arbitrary whitespace surrounding it is also accepted
    /// assert_eq!(ident.parse(" \t \n  \t   world  \t  ").into_result(), Ok("world"));
    /// ```
    fn padded(self) -> Ext<Padded<Self>>
    where
        Self: Sized,
        I: Input<'a>,
        I::Token: Char,
    {
        Ext(Padded { parser: self })
    }
}

impl<'a, I, O, E, P> ParserExt<'a, I, O, E> for P
where
    I: Input<'a>,
    E: extra::ParserExtra<'a, I>,
    P: Parser<'a, I, O, E>,
{
}

/// A parser that accepts (and ignores) any number of whitespace characters before or after another pattern.
#[derive(Copy, Clone)]
pub struct Padded<A> {
    pub(crate) parser: A,
}

impl<'a, I, O, E, A> ExtParser<'a, I, O, E> for Padded<A>
where
    I: ValueInput<'a>,
    E: extra::ParserExtra<'a, I>,
    I::Token: Char,
    A: Parser<'a, I, O, E>,
{
    fn parse(&self, inp: &mut InputRef<'a, '_, I, E>) -> Result<O, E::Error> {
        inp.skip_while(|c| c.is_whitespace());
        let out = inp.parse(&self.parser)?;
        inp.skip_while(|c| c.is_whitespace());
        Ok(out)
    }
}
