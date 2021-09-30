use super::*;

pub trait Strategy<I: Clone, O> {
    fn recover<P: Parser<I, O>>(&self, parser: P, stream: &mut StreamOf<I, P::Error>) -> PResult<O, P::Error>;
}

#[derive(Copy, Clone)]
pub struct SkipThenRetryUntil<I, const N: usize>(pub [I; N]);

impl<I: Clone + PartialEq, O, const N: usize> Strategy<I, O> for SkipThenRetryUntil<I, N> {
    fn recover<P: Parser<I, O>>(&self, parser: P, stream: &mut StreamOf<I, P::Error>) -> PResult<O, P::Error> {
        match { #[allow(deprecated)] parser.try_parse_inner(stream) } {
            (a_errors, Ok(a_out)) => (a_errors, Ok(a_out)),
            (a_errors, Err(a_err)) => {
                loop {
                    if !stream.attempt(|stream| if stream.next().2.map_or(true, |tok| self.0.contains(&tok)) {
                        (false, false)
                    } else {
                        (true, true)
                    }) {
                        break (a_errors, Err(a_err));
                    }
                    #[allow(deprecated)]
                    let (mut errors, res) = parser.parse_inner(stream);
                    if let Ok(out) = res {
                        errors.push(a_err);
                        break (errors, Ok(out));
                    }
                }
            },
        }
    }
}

#[derive(Copy, Clone)]
pub struct NestedDelimiters<I, F>(pub I, pub I, pub F);

impl<I: Clone + PartialEq, O, F: Fn() -> O> Strategy<I, O> for NestedDelimiters<I, F> {
    fn recover<P: Parser<I, O>>(&self, parser: P, stream: &mut StreamOf<I, P::Error>) -> PResult<O, P::Error> {
        assert!(self.0 != self.1, "NestedDelimiters cannot be used with identical delimiters.");
        match { #[allow(deprecated)] parser.try_parse_inner(stream) } {
            (a_errors, Ok(a_out)) => (a_errors, Ok(a_out)),
            (mut a_errors, Err(a_err)) => {
                let mut balance = 0;
                if loop {
                    if match stream.next() {
                        (_, _, Some(t)) if t == self.0 => { balance += 1; true },
                        (_, _, Some(t)) if t == self.1 => { balance -= 1; true },
                        (_, _, Some(_)) => false,
                        (_, _, None) => break false,
                    } {
                        if balance == 0 {
                            break true;
                        } else if balance < 0 {
                            // The end of a delimited section is not a valid recovery pattern
                            break false;
                        }
                    } else if balance == 0 {
                        // A non-delimiter token before anything else is not a valid recovery pattern
                        break false;
                    }
                } {
                    a_errors.push(a_err);
                    (a_errors, Ok(((self.2)(), None)))
                } else {
                    (a_errors, Err(a_err))
                }
            },
        }
    }
}

#[derive(Copy, Clone)]
pub struct Recovery<A, S>(pub(crate) A, pub(crate) S);

impl<I: Clone, O, A: Parser<I, O, Error = E>, S: Strategy<I, O>, E: Error<Token = I>> Parser<I, O> for Recovery<A, S> {
    type Error = E;

    fn parse_inner(&self, stream: &mut StreamOf<I, Self::Error>) -> PResult<O, Self::Error> {
        self.1.recover(&self.0, stream)
    }
}
