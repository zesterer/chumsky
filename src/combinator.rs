use super::*;

/// See [`Parser::ignored`].
pub type Ignored<P, O> = To<P, O, ()>;

/// See [`Parser::padding_for`].
pub type PaddingFor<A, B, O, U> = Map<Then<A, B>, fn((O, U)) -> U, (O, U)>;

/// See [`Parser::padded_by`].
pub type PaddedBy<A, B, O, U> = Map<Then<A, B>, fn((O, U)) -> O, (O, U)>;

/// See [`Parser::or`].
#[derive(Copy, Clone)]
pub struct Or<A, B>(pub(crate) A, pub(crate) B);

impl<I: Clone, O, A: Parser<I, O, Error =  E>, B: Parser<I, O, Error = E>, E: Error<I>> Parser<I, O> for Or<A, B> {
    type Error = E;

    fn parse_inner<S: Stream<I, <Self::Error as Error<I>>::Span>>(&self, stream: &mut S, errors: &mut Vec<Self::Error>) -> (usize, Result<(O, Option<E>), E>) {
        match self.0.parse_inner(stream, errors) {
            (n, Ok((o, f))) => (n, Ok((o, f))),
            (0, Err(e)) => match self.1.parse_inner(stream, errors) {
                (m, Ok((o, g))) => (m, Ok((o, g))),
                (m, Err(f)) => (m, Err(e.merge(f))),
            },
            (n, Err(e)) => (n, Err(e)),
        }
    }
}

/// See [`Parser::or_not`].
#[derive(Copy, Clone)]
pub struct OrNot<A>(pub(crate) A);

impl<I: Clone, O, A: Parser<I, O, Error =  E>, E: Error<I>> Parser<I, Option<O>> for OrNot<A> {
    type Error = E;

    fn parse_inner<S: Stream<I, <Self::Error as Error<I>>::Span>>(&self, stream: &mut S, errors: &mut Vec<Self::Error>) -> (usize, Result<(Option<O>, Option<E>), E>) {
        match self.0.parse_inner(stream, errors) {
            (n, Ok((o, f))) => (n, Ok((Some(o), f))),
            (0, Err(e)) => (0, Ok((None, Some(e)))),
            (n, Err(e)) => (n, Err(e)),
        }
    }
}

/// See [`Parser::then`].
#[derive(Copy, Clone)]
pub struct Then<A, B>(pub(crate) A, pub(crate) B);

impl<I, O, U, A: Parser<I, O, Error = E>, B: Parser<I, U, Error = E>, E: Error<I>> Parser<I, (O, U)> for Then<A, B> {
    type Error = E;

    fn parse_inner<S: Stream<I, <Self::Error as Error<I>>::Span>>(&self, stream: &mut S, errors: &mut Vec<Self::Error>) -> (usize, Result<((O, U), Option<E>), E>) {
        match self.0.parse_inner(stream, errors) {
            (n, Ok((o, f))) => match self.1.parse_inner(stream, errors) {
                (m, Ok((u, g))) => (n + m, Ok(((o, u), or_zip_with(f, g, |f, g| f.merge(g))))),
                (m, Err(e)) => (n + m, Err(zip_or(f, e, |f, e| f.merge(e)))),
            },
            (n, Err(e)) => (n, Err(e)),
        }
    }
}

/*
/// See [`Parser::then_catch`].
#[derive(Copy, Clone)]
pub struct ThenCatch<A, I>(pub(crate) A, pub(crate) I);

impl<I: Clone + PartialEq, O, A: Parser<I, O, Error = E>, E: Error<I>> Parser<I, Option<O>> for ThenCatch<A, I> {
    type Error = E;

    fn parse_inner<S: Stream<I, <Self::Error as Error<I>>::Span>>(&self, stream: &mut S, errors: &mut Vec<Self::Error>) -> (usize, Result<(Option<O>, Option<E>), E>) {
        let (mut n, mut res) = self.0.parse_inner(stream, errors);

        assert!(n > 0 /*|| res.is_ok()*/, "ThenCatch must consume input (i.e: be non-optional) to avoid consuming everything");

        loop {
            n += 1;
            match stream.next() {
                Some(x) if x == self.1 => match res {
                    Ok((o, f)) => break (n, Ok((Some(o), f))),
                    Err(e) => {
                        errors.push(e);
                        break (n, Ok((None, None)));
                    },
                },
                Some(x) => res = Err(res.err().unwrap_or_else(|| E::expected_found(stream.position(), vec![self.1.clone()], Some(x)))),
                None => break (n, Err(res.err().unwrap_or_else(|| E::expected_found(stream.position(), vec![self.1.clone()], None)))),
            }
        }
    }
}
*/

/// See [`Parser::delimited_by`].
#[derive(Copy, Clone)]
pub struct DelimitedBy<A, I>(pub(crate) A, pub(crate) I, pub(crate) I);

impl<I: Clone + PartialEq, O, A: Parser<I, O, Error = E>, E: Error<I>> Parser<I, Option<O>> for DelimitedBy<A, I> {
    type Error = E;

    fn parse_inner<S: Stream<I, <Self::Error as Error<I>>::Span>>(&self, stream: &mut S, errors: &mut Vec<Self::Error>) -> (usize, Result<(Option<O>, Option<E>), E>) {
        let mut n = match stream.peek_token() {
            Some(x) if x == &self.1 => { stream.next(); 1 },
            x => {
                let x = x.cloned();
                return (0, Err(E::expected_token_found(stream.peek_span(), vec![self.1.clone()], x)))
            },
        };

        let (m, res) = self.0.parse_inner(stream, errors);
        n += m;

        let (output, mut furthest) = match res {
            Ok((o, furthest)) => (Some(o), furthest),
            Err(e) => (None, Some(e)),
        };

        let mut balance = 0;
        let mut is_err = output.is_none();
        loop {
            n += 1;
            let token = match stream.next() {
                Some(x) if x == self.1 => { balance -= 1; x },
                Some(x) if x == self.2 => if balance == 0 {
                    break if is_err {
                        errors.push(furthest.unwrap());
                        (n, Ok((None, None)))
                    } else {
                        (n, Ok((output, None)))
                    };
                } else {
                    balance += 1;
                    x
                },
                Some(x) => x,
                None => break (n, Err(furthest.unwrap_or_else(|| E::expected_token_found(stream.last_span(), vec![self.2.clone()], None)))),
            };

            if !is_err {
                furthest = Some(zip_or(furthest, E::expected_token_found(stream.last_span(), vec![self.2.clone()], Some(token)), |a, b| a.merge(b)));
                is_err = true;
            }
        }
    }
}

/// See [`Parser::repeated`] and [`Parser::repeated_at_least`].
#[derive(Copy, Clone)]
pub struct Repeated<A>(pub(crate) A, pub(crate) usize);

impl<I, O, A: Parser<I, O, Error = E>, E: Error<I>> Parser<I, Vec<O>> for Repeated<A> {
    type Error = E;

    fn parse_inner<S: Stream<I, <Self::Error as Error<I>>::Span>>(&self, stream: &mut S, errors: &mut Vec<Self::Error>) -> (usize, Result<(Vec<O>, Option<E>), E>) {
        let mut outputs = Vec::new();
        let mut furthest = None;

        let mut n = 0;
        loop {
            match self.0.parse_inner(stream, errors) {
                (m, Ok((o, f))) => {
                    outputs.push(o);
                    furthest = or_zip_with(furthest, f, |a, b| a.merge(b));
                    n += m;
                },
                (0, Err(f)) if outputs.len() >= self.1 => break (n, Ok((outputs, Some(zip_or(furthest, f, |a, b| a.merge(b)))))),
                (0, Err(e)) => break (n, Err(e)),
                (m, Err(e)) => break (n + m, Err(e)),
            }
        }
    }
}

/// See [`Parser::map`].
pub struct Map<A, F, O>(pub(crate) A, pub(crate) F, pub(crate) PhantomData<O>);

impl<A: Copy, F: Copy, O> Copy for Map<A, F, O> {}
impl<A: Clone, F: Clone, O> Clone for Map<A, F, O> {
    fn clone(&self) -> Self { Self(self.0.clone(), self.1.clone(), PhantomData) }
}

impl<I, O, A: Parser<I, O, Error = E>, U, F: Fn(O) -> U, E: Error<I>> Parser<I, U> for Map<A, F, O> {
    type Error = E;

    fn parse_inner<S: Stream<I, <Self::Error as Error<I>>::Span>>(&self, stream: &mut S, errors: &mut Vec<Self::Error>) -> (usize, Result<(U, Option<E>), E>) {
        let (n, res) = self.0.parse_inner(stream, errors);
        (n, res.map(|(o, f)|((&self.1)(o), f)))
    }
}

/// See [`Parser::map_with_span`].
pub struct MapWithSpan<A, F, O>(pub(crate) A, pub(crate) F, pub(crate) PhantomData<O>);

impl<A: Copy, F: Copy, O> Copy for MapWithSpan<A, F, O> {}
impl<A: Clone, F: Clone, O> Clone for MapWithSpan<A, F, O> {
    fn clone(&self) -> Self { Self(self.0.clone(), self.1.clone(), PhantomData) }
}

impl<I, O, A: Parser<I, O, Error = E>, U, F: Fn(O, Option<E::Span>) -> U, E: Error<I>> Parser<I, U> for MapWithSpan<A, F, O> {
    type Error = E;

    fn parse_inner<S: Stream<I, <Self::Error as Error<I>>::Span>>(&self, stream: &mut S, errors: &mut Vec<Self::Error>) -> (usize, Result<(U, Option<E>), E>) {
        let start = stream.peek_span();
        let (n, res) = self.0.parse_inner(stream, errors);
        let span = match n {
            0 => stream
                .last_span()
                .into_iter()
                .zip(start)
                .map(|(start, end)| start.inner(end))
                .next(),
            _ => start
                .into_iter()
                .zip(stream.last_span())
                .map(|(start, end)| start.union(end))
                .next(),
        };
        (n, res.map(|(o, f)|((&self.1)(o, span), f)))
    }
}

/// See [`Parser::foldl`].
pub struct Foldl<A, F, O, U>(pub(crate) A, pub(crate) F, pub(crate) PhantomData<(O, U)>);

impl<A: Copy, F: Copy, O, U> Copy for Foldl<A, F, O, U> {}
impl<A: Clone, F: Clone, O, U> Clone for Foldl<A, F, O, U> {
    fn clone(&self) -> Self { Self(self.0.clone(), self.1.clone(), PhantomData) }
}

impl<I, O, A: Parser<I, (O, Vec<U>), Error = E>, U, F: Fn(O, U) -> O, E: Error<I>> Parser<I, O> for Foldl<A, F, O, U> {
    type Error = E;

    fn parse_inner<S: Stream<I, <Self::Error as Error<I>>::Span>>(&self, stream: &mut S, errors: &mut Vec<Self::Error>) -> (usize, Result<(O, Option<E>), E>) {
        let (n, res) = self.0.parse_inner(stream, errors);
        (n, res.map(|((head, tail), f)|(tail.into_iter().fold(head, &self.1), f)))
    }
}

/// See [`Parser::foldr`].
pub struct Foldr<A, F, O, U>(pub(crate) A, pub(crate) F, pub(crate) PhantomData<(O, U)>);

impl<A: Copy, F: Copy, O, U> Copy for Foldr<A, F, O, U> {}
impl<A: Clone, F: Clone, O, U> Clone for Foldr<A, F, O, U> {
    fn clone(&self) -> Self { Self(self.0.clone(), self.1.clone(), PhantomData) }
}

impl<I, O, A: Parser<I, (Vec<O>, U), Error = E>, U, F: Fn(O, U) -> U, E: Error<I>> Parser<I, U> for Foldr<A, F, O, U> {
    type Error = E;

    fn parse_inner<S: Stream<I, <Self::Error as Error<I>>::Span>>(&self, stream: &mut S, errors: &mut Vec<Self::Error>) -> (usize, Result<(U, Option<E>), E>) {
        let (n, res) = self.0.parse_inner(stream, errors);
        (n, res.map(|((init, end), f)|(init.into_iter().rev().fold(end, |b, a| (&self.1)(a, b)), f)))
    }
}

/// See [`Parser::map_err`].
#[derive(Copy, Clone)]
pub struct MapErr<A, F>(pub(crate) A, pub(crate) F);

impl<I, O, A: Parser<I, O, Error = E>, F: Fn(E) -> E, E: Error<I>> Parser<I, O> for MapErr<A, F> {
    type Error = E;

    fn parse_inner<S: Stream<I, <Self::Error as Error<I>>::Span>>(&self, stream: &mut S, errors: &mut Vec<Self::Error>) -> (usize, Result<(O, Option<E>), E>) {
        let (n, res) = self.0.parse_inner(stream, errors);
        (n, res.map_err(&self.1))
    }
}

/// See [`Parser::labelled`].
#[derive(Copy, Clone)]
pub struct Label<A, L>(pub(crate) A, pub(crate) L);

impl<I, O, A: Parser<I, O, Error = E>, L: Into<E::Pattern> + Clone, E: Error<I>> Parser<I, O> for Label<A, L> {
    type Error = E;

    fn parse_inner<S: Stream<I, <Self::Error as Error<I>>::Span>>(&self, stream: &mut S, errors: &mut Vec<Self::Error>) -> (usize, Result<(O, Option<E>), E>) {
        let (n, res) = self.0.parse_inner(stream, errors);
        (n, res.map_err(|e| e.into_labelled(self.1.clone())))
    }
}

/// See [`Parser::to`].
pub struct To<A, O, U>(pub(crate) A, pub(crate) U, pub(crate) PhantomData<O>);

impl<A: Copy, U: Copy, O> Copy for To<A, O, U> {}
impl<A: Clone, U: Clone, O> Clone for To<A, O, U> {
    fn clone(&self) -> Self { Self(self.0.clone(), self.1.clone(), PhantomData) }
}

impl<I, O, A: Parser<I, O, Error = E>, U: Clone, E: Error<I>> Parser<I, U> for To<A, O, U> {
    type Error = E;

    fn parse_inner<S: Stream<I, <Self::Error as Error<I>>::Span>>(&self, stream: &mut S, errors: &mut Vec<Self::Error>) -> (usize, Result<(U, Option<E>), E>) {
        let (n, res) = self.0.parse_inner(stream, errors);
        (n, res.map(|(_, f)| (self.1.clone(), f)))
    }
}
