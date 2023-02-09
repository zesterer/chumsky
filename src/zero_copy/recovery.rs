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

/// A recovery parser that searches for a start and end delimiter, respecting nesting.
///
/// It is possible to specify additional delimiter pairs that are valid in the pattern's context for better errors. For
/// example, you might want to also specify `[('[', ']'), ('{', '}')]` when recovering a parenthesised expression as
/// this can aid in detecting delimiter mismatches.
///
/// A function that generates a fallback output on recovery is also required.
pub fn nested_delimiters<'a, I, O, E, F, const N: usize>(
    start: I::Token,
    end: I::Token,
    others: [(I::Token, I::Token); N],
    fallback: F,
) -> impl Parser<'a, I, O, E> + Clone
where
    I: Input + ?Sized + 'a,
    I::Token: PartialEq + Clone,
    E: extra::ParserExtra<'a, I>,
    F: Fn(I::Span) -> O + Clone,
{
    // TODO: Does this actually work? TESTS!
    recursive({
        let (start, end) = (start.clone(), end.clone());
        |block| {
            let mut many_block = block
                .clone()
                .delimited_by(just(start.clone()), just(end.clone()))
                .boxed();
            for (s, e) in &others {
                many_block = many_block
                    .or(block.clone().delimited_by(just(s.clone()), just(e.clone())))
                    .boxed();
            }

            let mut skip = core::array::IntoIter::new([start, end])
                .into_iter()
                .chain(core::array::IntoIter::new(others).flat_map(|(s, e)| [s, e]))
                .collect::<Vec<_>>();

            many_block
                .or(any().and_is(none_of(skip)).ignored())
                .repeated()
        }
    })
    .delimited_by(just(start), just(end))
    .map_with_span(move |_, span| fallback(span))
}
