//! Types and traits that facilitate error recovery.
//!
//! *“Do you find coming to terms with the mindless tedium of it all presents an interesting challenge?”*

use super::*;

/// A trait implemented by error recovery strategies.
pub trait Strategy<I: Clone, O, E: Error<I>> {
    /// Recover from a parsing failure.
    fn recover<D: Debugger, P: Parser<I, O, Error = E>>(
        &self,
        recovered_errors: Vec<Located<I, P::Error>>,
        fatal_error: Located<I, P::Error>,
        parser: P,
        debugger: &mut D,
        stream: &mut StreamOf<I, P::Error>,
    ) -> PResult<I, O, P::Error>;
}

/// See [`skip_then_retry_until`].
#[must_use]
#[derive(Copy, Clone)]
pub struct SkipThenRetryUntil<I, const N: usize>(
    pub(crate) [I; N],
    pub(crate) bool,
    pub(crate) bool,
);

impl<I, const N: usize> SkipThenRetryUntil<I, N> {
    /// Alters this recovery strategy so that the first token will always be skipped.
    ///
    /// This is useful when the input being searched for also appears at the beginning of the pattern that failed to
    /// parse.
    pub fn skip_start(self) -> Self {
        Self(self.0, self.1, true)
    }

    /// Alters this recovery strategy so that the synchronisation token will be consumed during recovery.
    ///
    /// This is useful when the input being searched for is a delimiter of a prior pattern rather than the start of a
    /// new pattern and hence is no longer important once recovery has occurred.
    pub fn consume_end(self) -> Self {
        Self(self.0, true, self.2)
    }
}

impl<I: Clone + PartialEq, O, E: Error<I>, const N: usize> Strategy<I, O, E>
    for SkipThenRetryUntil<I, N>
{
    fn recover<D: Debugger, P: Parser<I, O, Error = E>>(
        &self,
        a_errors: Vec<Located<I, P::Error>>,
        a_err: Located<I, P::Error>,
        parser: P,
        debugger: &mut D,
        stream: &mut StreamOf<I, P::Error>,
    ) -> PResult<I, O, P::Error> {
        if self.2 {
            let _ = stream.next();
        }
        loop {
            #[allow(deprecated)]
            let (mut errors, res) = stream.try_parse(|stream| {
                #[allow(deprecated)]
                debugger.invoke(&parser, stream)
            });
            if let Ok(out) = res {
                errors.push(a_err);
                break (errors, Ok(out));
            }
            #[allow(clippy::blocks_in_if_conditions)]
            if !stream.attempt(
                |stream| match stream.next().2.map(|tok| self.0.contains(&tok)) {
                    Some(true) => (self.1, false),
                    Some(false) => (true, true),
                    None => (false, false),
                },
            ) {
                break (a_errors, Err(a_err));
            }
        }
    }
}

/// A recovery mode that simply skips to the next input on parser failure and tries again, until reaching one of
/// several inputs.
///
/// Also see [`SkipThenRetryUntil::consume_end`].
///
/// This strategy is very 'stupid' and can result in very poor error generation in some languages. Place this strategy
/// after others as a last resort, and be careful about over-using it.
pub fn skip_then_retry_until<I, const N: usize>(until: [I; N]) -> SkipThenRetryUntil<I, N> {
    SkipThenRetryUntil(until, false, true)
}

/// See [`skip_until`].
#[must_use]
#[derive(Copy, Clone)]
pub struct SkipUntil<I, F, const N: usize>(
    pub(crate) [I; N],
    pub(crate) F,
    pub(crate) bool,
    pub(crate) bool,
);

impl<I, F, const N: usize> SkipUntil<I, F, N> {
    /// Alters this recovery strategy so that the first token will always be skipped.
    ///
    /// This is useful when the input being searched for also appears at the beginning of the pattern that failed to
    /// parse.
    pub fn skip_start(self) -> Self {
        Self(self.0, self.1, self.2, true)
    }

    /// Alters this recovery strategy so that the synchronisation token will be consumed during recovery.
    ///
    /// This is useful when the input being searched for is a delimiter of a prior pattern rather than the start of a
    /// new pattern and hence is no longer important once recovery has occurred.
    pub fn consume_end(self) -> Self {
        Self(self.0, self.1, true, self.3)
    }
}

impl<I: Clone + PartialEq, O, F: Fn(E::Span) -> O, E: Error<I>, const N: usize> Strategy<I, O, E>
    for SkipUntil<I, F, N>
{
    fn recover<D: Debugger, P: Parser<I, O, Error = E>>(
        &self,
        mut a_errors: Vec<Located<I, P::Error>>,
        a_err: Located<I, P::Error>,
        _parser: P,
        _debugger: &mut D,
        stream: &mut StreamOf<I, P::Error>,
    ) -> PResult<I, O, P::Error> {
        let pre_state = stream.save();
        if self.3 {
            let _ = stream.next();
        }
        a_errors.push(a_err);
        loop {
            match stream.attempt(|stream| {
                let (at, span, tok) = stream.next();
                match tok.map(|tok| self.0.contains(&tok)) {
                    Some(true) => (self.2, Ok(true)),
                    Some(false) => (true, Ok(false)),
                    None => (true, Err((at, span))),
                }
            }) {
                Ok(true) => break (a_errors, Ok(((self.1)(stream.span_since(pre_state)), None))),
                Ok(false) => {}
                Err(_) if stream.save() > pre_state => {
                    break (a_errors, Ok(((self.1)(stream.span_since(pre_state)), None)))
                }
                Err((at, span)) => {
                    break (
                        a_errors,
                        Err(Located::at(
                            at,
                            E::expected_input_found(span, self.0.iter().cloned().map(Some), None),
                        )),
                    )
                }
            }
        }
    }
}

/// A recovery mode that skips input until one of several inputs is found.
///
/// Also see [`SkipUntil::consume_end`].
///
/// This strategy is very 'stupid' and can result in very poor error generation in some languages. Place this strategy
/// after others as a last resort, and be careful about over-using it.
pub fn skip_until<I, F, const N: usize>(until: [I; N], fallback: F) -> SkipUntil<I, F, N> {
    SkipUntil(until, fallback, false, false)
}

/// See [`nested_delimiters`].
#[must_use]
#[derive(Copy, Clone)]
pub struct NestedDelimiters<I, F, const N: usize>(
    pub(crate) I,
    pub(crate) I,
    pub(crate) [(I, I); N],
    pub(crate) F,
);

impl<I: Clone + PartialEq, O, F: Fn(E::Span) -> O, E: Error<I>, const N: usize> Strategy<I, O, E>
    for NestedDelimiters<I, F, N>
{
    // This looks like something weird with clippy, it warns in a weird spot and isn't fixed by
    // marking it at the spot.
    #[allow(clippy::blocks_in_if_conditions)]
    fn recover<D: Debugger, P: Parser<I, O, Error = E>>(
        &self,
        mut a_errors: Vec<Located<I, P::Error>>,
        a_err: Located<I, P::Error>,
        _parser: P,
        _debugger: &mut D,
        stream: &mut StreamOf<I, P::Error>,
    ) -> PResult<I, O, P::Error> {
        let mut balance = 0;
        let mut balance_others = [0; N];
        let mut starts = Vec::new();
        let mut error = None;
        let pre_state = stream.save();
        let recovered = loop {
            if match stream.next() {
                (_, span, Some(t)) if t == self.0 => {
                    balance += 1;
                    starts.push(span);
                    true
                }
                (_, _, Some(t)) if t == self.1 => {
                    balance -= 1;
                    starts.pop();
                    true
                }
                (at, span, Some(t)) => {
                    for (balance_other, others) in balance_others.iter_mut().zip(self.2.iter()) {
                        if t == others.0 {
                            *balance_other += 1;
                        } else if t == others.1 {
                            *balance_other -= 1;

                            if *balance_other < 0 && balance == 1 {
                                // stream.revert(pre_state);
                                error.get_or_insert_with(|| {
                                    Located::at(
                                        at,
                                        P::Error::unclosed_delimiter(
                                            starts.pop().unwrap(),
                                            self.0.clone(),
                                            span.clone(),
                                            self.1.clone(),
                                            Some(t.clone()),
                                        ),
                                    )
                                });
                            }
                        }
                    }
                    false
                }
                (at, span, None) => {
                    if balance > 0 && balance == 1 {
                        error.get_or_insert_with(|| match starts.pop() {
                            Some(start) => Located::at(
                                at,
                                P::Error::unclosed_delimiter(
                                    start,
                                    self.0.clone(),
                                    span,
                                    self.1.clone(),
                                    None,
                                ),
                            ),
                            None => Located::at(
                                at,
                                P::Error::expected_input_found(
                                    span,
                                    Some(Some(self.1.clone())),
                                    None,
                                ),
                            ),
                        });
                    }
                    break false;
                }
            } {
                match balance.cmp(&0) {
                    Ordering::Equal => break true,
                    // The end of a delimited section is not a valid recovery pattern
                    Ordering::Less => break false,
                    Ordering::Greater => (),
                }
            } else if balance == 0 {
                // A non-delimiter input before anything else is not a valid recovery pattern
                break false;
            }
        };

        if let Some(e) = error {
            a_errors.push(e);
        }

        if recovered {
            if a_errors.last().map_or(true, |e| a_err.at < e.at) {
                a_errors.push(a_err);
            }
            (a_errors, Ok(((self.3)(stream.span_since(pre_state)), None)))
        } else {
            (a_errors, Err(a_err))
        }
    }
}

/// A recovery strategy that searches for a start and end delimiter, respecting nesting.
///
/// It is possible to specify additional delimiter pairs that are valid in the pattern's context for better errors. For
/// example, you might want to also specify `[('[', ']'), ('{', '}')]` when recovering a parenthesised expression as
/// this can aid in detecting delimiter mismatches.
///
/// A function that generates a fallback output on recovery is also required.
pub fn nested_delimiters<I: PartialEq, F, const N: usize>(
    start: I,
    end: I,
    others: [(I, I); N],
    fallback: F,
) -> NestedDelimiters<I, F, N> {
    assert!(
        start != end,
        "Start and end delimiters cannot be the same when using `NestedDelimiters`"
    );
    NestedDelimiters(start, end, others, fallback)
}

/// See [`skip_parser`].
#[derive(Copy, Clone)]
pub struct SkipParser<R>(pub(crate) R);

impl<I: Clone + PartialEq, O, R: Parser<I, O, Error = E>, E: Error<I>> Strategy<I, O, E>
    for SkipParser<R>
{
    fn recover<D: Debugger, P: Parser<I, O, Error = E>>(
        &self,
        mut a_errors: Vec<Located<I, P::Error>>,
        a_err: Located<I, P::Error>,
        _parser: P,
        debugger: &mut D,
        stream: &mut StreamOf<I, P::Error>,
    ) -> PResult<I, O, P::Error> {
        a_errors.push(a_err);

        let (mut errors, res) = self.0.parse_inner(debugger, stream);
        a_errors.append(&mut errors);
        (a_errors, res)
    }
}

/// A recovery mode that applies the provided recovery parser to determine the content to skip.
///
/// ```
/// # use chumsky::prelude::*;
/// #[derive(Clone, Debug, PartialEq, Eq, Hash)]
/// enum Token {
///     GoodKeyword,
///     BadKeyword,
///     Newline,
/// }
///
/// #[derive(Clone, Debug, PartialEq, Eq, Hash)]
/// enum AST {
///     GoodLine,
///     Error,
/// }
///
/// // The happy path...
/// let goodline = just::<Token, _, Simple<_>>(Token::GoodKeyword)
///     .ignore_then(none_of(Token::Newline).repeated().to(AST::GoodLine))
///     .then_ignore(just(Token::Newline));
///
/// // If it fails, swallow everything up to a newline, but only if the line
/// // didn't contain BadKeyword which marks an alternative parse route that
/// // we want to accept instead.
/// let goodline_with_recovery = goodline.recover_with(skip_parser(
///     none_of([Token::Newline, Token::BadKeyword])
///         .repeated()
///         .then_ignore(just(Token::Newline))
///         .to(AST::Error),
/// ));
/// ```

pub fn skip_parser<R>(recovery_parser: R) -> SkipParser<R> {
    SkipParser(recovery_parser)
}

/// A parser that includes a fallback recovery strategy should parsing result in an error.
#[must_use]
#[derive(Copy, Clone)]
pub struct Recovery<A, S>(pub(crate) A, pub(crate) S);

impl<I: Clone, O, A: Parser<I, O, Error = E>, S: Strategy<I, O, E>, E: Error<I>> Parser<I, O>
    for Recovery<A, S>
{
    type Error = E;

    fn parse_inner<D: Debugger>(
        &self,
        debugger: &mut D,
        stream: &mut StreamOf<I, E>,
    ) -> PResult<I, O, E> {
        match stream.try_parse(|stream| {
            #[allow(deprecated)]
            debugger.invoke(&self.0, stream)
        }) {
            (a_errors, Ok(a_out)) => (a_errors, Ok(a_out)),
            (a_errors, Err(a_err)) => self.1.recover(a_errors, a_err, &self.0, debugger, stream),
        }
    }

    fn parse_inner_verbose(&self, d: &mut Verbose, s: &mut StreamOf<I, E>) -> PResult<I, O, E> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
    fn parse_inner_silent(&self, d: &mut Silent, s: &mut StreamOf<I, E>) -> PResult<I, O, E> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
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
