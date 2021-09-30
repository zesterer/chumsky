use super::*;

pub trait Strategy<I, O, E: Error> {
    fn recover(&self, stream: &mut StreamOf<I, E>) -> Result<(), ()>;
}

#[derive(Copy, Clone)]
pub struct Until<I, const N: usize>(pub [I; N]);

impl<I: Clone + PartialEq, O, E: Error, const N: usize> Strategy<I, O, E> for Until<I, N> {
    fn recover(&self, stream: &mut StreamOf<I, E>) -> Result<(), ()> {
        let mut n = 0;
        while stream.attempt(|stream| match stream.next() {
            (_, _, Some(tok)) if !self.0.contains(&tok) => (true, Ok(())),
            _ => (false, Err(())),
        }).is_ok() { n += 1; }
        if n > 0 {
            Ok(())
        } else {
            Err(())
        }
    }
}

#[derive(Copy, Clone)]
pub struct SkipExcept<I, const N: usize>(pub [I; N]);

impl<I: Clone + PartialEq, O, E: Error, const N: usize> Strategy<I, O, E> for SkipExcept<I, N> {
    fn recover(&self, stream: &mut StreamOf<I, E>) -> Result<(), ()> {
        stream.attempt(|stream| match stream.next() {
            (_, _, Some(tok)) if !self.0.contains(&tok) => (true, Ok(())),
            _ => (false, Err(())),
        })
    }
}

// impl<I, O, P: Parser<I, O>, E: Error> Strategy<I, O, E> for P {
//     fn recover(&self, stream: &mut StreamOf<I, E>) -> Result<(), ()> {
//         self.parse_inner(stream).1.map(|_| ()).map_err(|_| ())
//     }
// }

#[derive(Copy, Clone)]
pub struct NestedDelimiters<I>(pub I, pub I);

impl<I: Clone + PartialEq, O, E: Error> Strategy<I, O, E> for NestedDelimiters<I> {
    fn recover(&self, stream: &mut StreamOf<I, E>) -> Result<(), ()> {
        let mut balance = 0;
        loop {
            if match stream.next() {
                (_, _, Some(t)) if t == self.0 => { balance += 1; true },
                (_, _, Some(t)) if t == self.1 => { balance -= 1; true },
                (_, _, Some(_)) => false,
                (_, _, None) => break Err(()),
            } {
                if balance == 0 {
                    break Ok(());
                } else if balance < 0 {
                    // The end of a delimited section is not a valid recovery pattern
                    break Err(());
                }
            } else if balance == 0 {
                // A non-delimiter token before anything else is not a valid recovery pattern
                break Err(());
            }
        }
    }
}

#[derive(Copy, Clone)]
pub struct Recovery<A, S, F>(pub(crate) A, pub(crate) S, pub(crate) F);

impl<I: Clone, O, A: Parser<I, O, Error = E>, S: Strategy<I, O, E>, F: Fn() -> O, E: Error<Token = I>> Parser<I, O> for Recovery<A, S, F> {
    type Error = E;

    fn parse_inner(&self, stream: &mut StreamOf<I, Self::Error>) -> PResult<O, Self::Error> {
        let at = stream.save();
        match self.0.try_parse_inner(stream) {
            (a_errors, Ok(a_out)) => (a_errors, Ok(a_out)),
            (mut a_errors, Err(a_err)) => {
                debug_assert_eq!(at, stream.save());

                // TODO: Is attempt needed here? Probably not because we allow invalid parses to mutate stream state.
                let res = stream.attempt(|stream| {
                    if self.1.recover(stream).is_ok() {
                        a_errors.push(a_err);
                        (true, (a_errors, Ok(((self.2)(), None))))
                    } else {
                        (false, (a_errors, Err(a_err)))
                    }
                });

                res
            },
        }
    }
}
