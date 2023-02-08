//! Types and functions that relate to error recovery.

use super::*;

/// See [`Parser::recover_with`].
#[derive(Copy, Clone)]
pub struct RecoverWith<A, F> {
    pub(crate) parser: A,
    pub(crate) fallback: F,
}

impl<'a, I, O, E, A, F> Parser<'a, I, O, E> for RecoverWith<A, F>
where
    I: Input + ?Sized,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E>,
    F: Parser<'a, I, O, E>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O, E::Error> {
        let before = inp.save();
        match self.parser.go::<M>(inp) {
            Ok(out) => Ok(out),
            Err(e) => {
                inp.rewind(before);
                match self.fallback.go::<M>(inp) {
                    Ok(out) => {
                        inp.emit(e.err);
                        Ok(out)
                    }
                    Err(_) => Err(e),
                }
            }
        }
    }

    go_extra!(O);
}

/// A recovery parser that skips input until one of several inputs is found.
///
/// This strategy is very 'stupid' and can result in very poor error generation in some languages. Place this strategy
/// after others as a last resort, and be careful about over-using it.
pub fn skip_until<'a, P, I, O, E>(pattern: P) -> impl Parser<'a, I, O, E> + Clone
where
    I: Input + ?Sized,
    P: Parser<'a, I, O, E> + Clone,
    E: extra::ParserExtra<'a, I>,
{
    any()
        .and_is(pattern.clone().not())
        .repeated()
        .ignore_then(pattern)
}
