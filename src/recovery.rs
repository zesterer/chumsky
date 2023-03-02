//! Types and functions that relate to error recovery.

use super::*;

/// A trait implemented by error recovery strategies. See [`Parser::recover_with`].
pub trait Strategy<'a, I: Input<'a>, O, E: ParserExtra<'a, I> = extra::Default> {
    // Attempt to recover from a parsing failure.
    // The strategy should properly handle the alt error but is not required to handle rewinding.
    #[doc(hidden)]
    fn recover<M: Mode, P: Parser<'a, I, O, E>>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        parser: &P,
    ) -> PResult<M, O>;
}

/// See [`via_parser`].
#[derive(Copy, Clone)]
pub struct ViaParser<A>(A);

/// Recover via the given recovery parser.
pub fn via_parser<A>(parser: A) -> ViaParser<A> {
    ViaParser(parser)
}

impl<'a, I, O, E, A> Strategy<'a, I, O, E> for ViaParser<A>
where
    I: Input<'a>,
    A: Parser<'a, I, O, E>,
    E: ParserExtra<'a, I>,
{
    fn recover<M: Mode, P: Parser<'a, I, O, E>>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        _parser: &P,
    ) -> PResult<M, O> {
        let alt = inp.errors.alt.take().expect("error but no alt?");
        let out = match self.0.go::<M>(inp) {
            Ok(out) => out,
            Err(()) => {
                inp.errors.alt = Some(alt);
                return Err(());
            }
        };
        inp.emit(alt.err);
        Ok(out)
    }
}

/// See [`Parser::recover_with`].
#[derive(Copy, Clone)]
pub struct RecoverWith<A, S> {
    pub(crate) parser: A,
    pub(crate) strategy: S,
}

impl<'a, I, O, E, A, S> Parser<'a, I, O, E> for RecoverWith<A, S>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    A: Parser<'a, I, O, E>,
    S: Strategy<'a, I, O, E>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        let before = inp.save();
        match self.parser.go::<M>(inp) {
            Ok(out) => Ok(out),
            Err(()) => {
                inp.rewind(before);
                match self.strategy.recover::<M, _>(inp, &self.parser) {
                    Ok(out) => Ok(out),
                    Err(()) => {
                        // Reset to before fallback attempt
                        inp.rewind(before);
                        Err(())
                    }
                }
            }
        }
    }

    go_extra!(O);
}

/// See [`skip_then_retry_until`].
#[must_use]
#[derive(Copy, Clone)]
pub struct SkipThenRetryUntil<A> {
    until: A,
}

impl<'a, I, O, E, A> Strategy<'a, I, O, E> for SkipThenRetryUntil<A>
where
    I: Input<'a>,
    A: Parser<'a, I, (), E>,
    E: ParserExtra<'a, I>,
{
    fn recover<M: Mode, P: Parser<'a, I, O, E>>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        parser: &P,
    ) -> PResult<M, O> {
        let alt = inp.errors.alt.take().expect("error but no alt?");
        loop {
            let before = inp.save();
            if let Ok(()) = self.until.go::<Check>(inp) {
                inp.errors.alt = Some(alt);
                break Err(());
            } else {
                inp.rewind(before);
            }

            let before = inp.offset();
            match inp.next() {
                (_, None) => {
                    inp.errors.alt = Some(alt);
                    break Err(());
                }
                (_, Some(tok)) => {
                    inp.emit(E::Error::expected_found(
                        None,
                        Some(tok),
                        // SAFETY: Using offsets derived from input
                        unsafe { inp.span_since(before) },
                    ));
                }
            }

            let before = inp.save();
            if let Ok(out) = parser.go::<M>(inp) {
                break Ok(out);
            } else {
                inp.rewind(before);
            }
        }
    }
}

/// TODO
pub fn skip_then_retry_until<A>(until: A) -> SkipThenRetryUntil<A> {
    SkipThenRetryUntil { until }
}

/// A recovery parser that skips input until one of several inputs is found.
///
/// This strategy is very 'stupid' and can result in very poor error generation in some languages. Place this strategy
/// after others as a last resort, and be careful about over-using it.
pub fn skip_until<'a, P, I, O, E>(pattern: P) -> impl Parser<'a, I, (), E> + Clone
where
    I: Input<'a>,
    P: Parser<'a, I, O, E> + Clone,
    E: extra::ParserExtra<'a, I>,
{
    any().and_is(pattern.clone().not()).repeated()
    // .ignore_then(pattern)
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
    I: Input<'a> + 'a,
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

            let skip = IntoIterator::into_iter([start, end])
                .into_iter()
                .chain(IntoIterator::into_iter(others).flat_map(|(s, e)| [s, e]))
                .collect::<Vec<_>>();

            many_block
                .or(any().and_is(none_of(skip)).ignored())
                .repeated()
        }
    })
    .delimited_by(just(start), just(end))
    .map_with_span(move |_, span| fallback(span))
}

#[cfg(test)]
mod tests {
    use crate::error::Cheap;
    use crate::prelude::*;

    #[test]
    fn recover_with_skip_then_retry_until() {
        let parser = just::<_, _, Cheap<_>>('a')
            .recover_with(skip_then_retry_until([',']))
            .separated_by(just(','));
        {
            let (result, errors) = parser.parse_recovery("a,a,2a,a");
            assert_eq!(result, Some(vec!['a', 'a', 'a', 'a']));
            assert_eq!(errors.len(), 1)
        }
        {
            let (result, errors) = parser.parse_recovery("a,a,2 a,a");
            assert_eq!(result, Some(vec!['a', 'a', 'a', 'a']));
            assert_eq!(errors.len(), 1)
        }
        {
            let (result, errors) = parser.parse_recovery("a,a,2  a,a");
            assert_eq!(result, Some(vec!['a', 'a', 'a', 'a']));
            assert_eq!(errors.len(), 1)
        }
    }

    #[test]
    fn until_nothing() {
        #[derive(Debug, Clone, Copy, PartialEq)]
        pub enum Token {
            Foo,
            Bar,
        }

        fn lexer() -> impl Parser<char, Token, Error = Simple<char>> {
            let foo = just("foo").to(Token::Foo);
            let bar = just("bar").to(Token::Bar);

            choice((foo, bar)).recover_with(skip_then_retry_until([]))
        }

        let (result, errors) = lexer().parse_recovery("baz");
        assert_eq!(result, None);
        assert_eq!(errors.len(), 1);
    }
}
