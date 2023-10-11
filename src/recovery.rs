//! Types and functions that relate to error recovery.

use super::*;

/// A trait implemented by error recovery strategies. See [`Parser::recover_with`].
///
/// This trait is sealed and so cannot be implemented by other crates because it has an unstable API. This may
/// eventually change. For now, if you wish to implement a new strategy, consider using [`via_parser`] or
/// [opening an issue/PR](https://github.com/zesterer/chumsky/issues/new).
pub trait Strategy<'a, I: Input<'a>, O, E: ParserExtra<'a, I> = extra::Default>: Sealed {
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

impl<A> Sealed for ViaParser<A> {}
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
        inp.emit(inp.offset, alt.err);
        Ok(out)
    }
}

/// See [`Parser::recover_with`].
#[derive(Copy, Clone)]
pub struct RecoverWith<A, S> {
    pub(crate) parser: A,
    pub(crate) strategy: S,
}

impl<'a, I, O, E, A, S> ParserSealed<'a, I, O, E> for RecoverWith<A, S>
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
pub struct SkipThenRetryUntil<S, U> {
    skip: S,
    until: U,
}

impl<S, U> Sealed for SkipThenRetryUntil<S, U> {}
impl<'a, I, O, E, S, U> Strategy<'a, I, O, E> for SkipThenRetryUntil<S, U>
where
    I: Input<'a>,
    S: Parser<'a, I, (), E>,
    U: Parser<'a, I, (), E>,
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
                inp.rewind(before);
                break Err(());
            } else {
                inp.rewind(before);
            }

            if let Err(()) = self.skip.go::<Check>(inp) {
                inp.errors.alt = Some(alt);
                break Err(());
            }

            let before = inp.save();
            if let Some(out) = parser.go::<M>(inp).ok().filter(|_| {
                inp.errors
                    .secondary_errors_since(before.err_count)
                    .is_empty()
            }) {
                inp.emit(inp.offset, alt.err);
                break Ok(out);
            } else {
                inp.errors.alt.take();
                inp.rewind(before);
            }
        }
    }
}

/// TODO
pub fn skip_then_retry_until<S, U>(skip: S, until: U) -> SkipThenRetryUntil<S, U> {
    SkipThenRetryUntil { skip, until }
}

/// See [`skip_until`].
#[must_use]
#[derive(Copy, Clone)]
pub struct SkipUntil<S, U, F> {
    skip: S,
    until: U,
    fallback: F,
}

impl<S, U, F> Sealed for SkipUntil<S, U, F> {}
impl<'a, I, O, E, S, U, F> Strategy<'a, I, O, E> for SkipUntil<S, U, F>
where
    I: Input<'a>,
    S: Parser<'a, I, (), E>,
    U: Parser<'a, I, (), E>,
    F: Fn() -> O,
    E: ParserExtra<'a, I>,
{
    fn recover<M: Mode, P: Parser<'a, I, O, E>>(
        &self,
        inp: &mut InputRef<'a, '_, I, E>,
        _parser: &P,
    ) -> PResult<M, O> {
        let alt = inp.errors.alt.take().expect("error but no alt?");
        loop {
            let before = inp.save();
            if let Ok(()) = self.until.go::<Check>(inp) {
                inp.emit(inp.offset, alt.err);
                break Ok(M::bind(|| (self.fallback)()));
            }
            inp.rewind(before);

            if let Err(()) = self.skip.go::<Check>(inp) {
                inp.errors.alt = Some(alt);
                break Err(());
            }
        }
    }
}

/// A recovery parser that skips input until one of several inputs is found.
///
/// This strategy is very 'stupid' and can result in very poor error generation in some languages. Place this strategy
/// after others as a last resort, and be careful about over-using it.
pub fn skip_until<S, U, F>(skip: S, until: U, fallback: F) -> SkipUntil<S, U, F> {
    SkipUntil {
        skip,
        until,
        fallback,
    }
}

/// A recovery parser that searches for a start and end delimiter, respecting nesting.
///
/// It is possible to specify additional delimiter pairs that are valid in the pattern's context for better errors. For
/// example, you might want to also specify `[('[', ']'), ('{', '}')]` when recovering a parenthesized expression as
/// this can aid in detecting delimiter mismatches.
///
/// A function that generates a fallback output on recovery is also required.
// TODO: Make this a strategy, add an unclosed_delimiter error
pub fn nested_delimiters<'a, I, O, E, F, const N: usize>(
    start: I::Token,
    end: I::Token,
    others: [(I::Token, I::Token); N],
    fallback: F,
) -> impl Parser<'a, I, O, E> + Clone
where
    I: ValueInput<'a>,
    I::Token: PartialEq + Clone + MaybeSync,
    E: extra::ParserExtra<'a, I> + MaybeSync,
    F: Fn(I::Span) -> O + Clone,
{
    // TODO: Does this actually work? TESTS!
    #[allow(clippy::tuple_array_conversions)]
    // Clippy is overly eager to fine pointless non-problems
    recursive({
        let (start, end) = (start.clone(), end.clone());
        |block| {
            let mut many_block = Parser::boxed(
                block
                    .clone()
                    .delimited_by(just(start.clone()), just(end.clone())),
            );
            for (s, e) in &others {
                many_block = Parser::boxed(
                    many_block.or(block.clone().delimited_by(just(s.clone()), just(e.clone()))),
                );
            }

            let skip = [start, end]
                .into_iter()
                .chain(IntoIterator::into_iter(others).flat_map(|(s, e)| [s, e]))
                .collect::<Vec<_>>();

            many_block
                .or(any().and_is(none_of(skip)).ignored())
                .repeated()
        }
    })
    .delimited_by(just(start), just(end))
    .map_with(move |_, e| fallback(e.span()))
}
