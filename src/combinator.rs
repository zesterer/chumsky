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

impl<I: Clone, O, A: Parser<I, O, Error = E>, B: Parser<I, O, Error = E>, E: Error<Token = I>> Parser<I, O> for Or<A, B> {
    type Error = E;

    fn parse_inner(&self, stream: &mut Stream<I>) -> PResult<O, Self::Error> {
        match self.0.try_parse_inner(stream) {
            (a_errors, Ok(a_out)) if a_errors.is_empty() => (a_errors, Ok(a_out)), // TODO: Handle merging alts with b
            (a_errors, a_out) => match self.1.try_parse_inner(stream) {
                (b_errors, Ok(b_out)) if b_errors.is_empty() => (b_errors, Ok(b_out)),
                (b_errors, b_out) => {
                    // Choose the branch that produced an output or, if not, the fewest errors
                    if a_errors.is_empty() && b_errors.is_empty() {
                        (Vec::new(), merge_results(a_out, b_out))
                    } else if (a_out.is_err(), a_errors.len()) < (b_out.is_err(), b_errors.len()) {
                        (a_errors, a_out)
                    } else {
                        (b_errors, b_out)
                    }
                },
            },
        }
    }
}

/// See [`Parser::or_not`].
#[derive(Copy, Clone)]
pub struct OrNot<A>(pub(crate) A);

impl<I: Clone, O, A: Parser<I, O, Error =  E>, E: Error<Token = I>> Parser<I, Option<O>> for OrNot<A> {
    type Error = E;

    fn parse_inner(&self, stream: &mut Stream<I>) -> PResult<Option<O>, Self::Error> {
        (&self.0).map(Some)
            .or(Parser::<I, _>::map(empty::<E>(), |_| None))
            .try_parse_inner(stream)
    }
}

/// See [`Parser::then`].
#[derive(Copy, Clone)]
pub struct Then<A, B>(pub(crate) A, pub(crate) B);

impl<I: Clone, O, U, A: Parser<I, O, Error = E>, B: Parser<I, U, Error = E>, E: Error<Token = I>> Parser<I, (O, U)> for Then<A, B> {
    type Error = E;

    fn parse_inner(&self, stream: &mut Stream<I>) -> PResult<(O, U), Self::Error> {
        match self.0.try_parse_inner(stream) {
            (mut a_errors, Ok((a_out, a_alt))) => match self.1.try_parse_inner(stream) {
                (mut b_errors, Ok((b_out, b_alt))) => {
                    (&mut a_errors).append(&mut b_errors);
                    (a_errors, Ok(((a_out, b_out), merge_alts(a_alt, b_alt))))
                },
                (mut b_errors, Err(b_err)) => {
                    (&mut a_errors).append(&mut b_errors);
                    (a_errors, Err(b_err.max(a_alt)))
                },
            },
            (a_errors, Err(a_err)) => (a_errors, Err(a_err)),
        }
    }
}

/*
/// See [`Parser::then_catch`].
#[derive(Copy, Clone)]
pub struct ThenCatch<A, I>(pub(crate) A, pub(crate) I);

impl<I: Clone + PartialEq, O, A: Parser<I, O, Error = E>, E: Error<Token = I>> Parser<I, Option<O>> for ThenCatch<A, I> {
    type Error = E;

    fn parse_inner<S: Stream<I, <Self::Error as Error>::Span>>(&self, stream: &mut S, errors: &mut Vec<Self::Error>) -> (usize, Result<(Option<O>, Option<E>), E>) {
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

impl<I: Clone + PartialEq, O, A: Parser<I, O, Error = E>, E: Error<Token = I>> Parser<I, O> for DelimitedBy<A, I> {
    type Error = E;

    fn parse_inner(&self, stream: &mut Stream<I>) -> PResult<O, Self::Error> {
        // TODO: Don't clone!
        just(self.1.clone())
            .then(&self.0)
            .then(just(self.2.clone()))
            .map(|((_, out), _)| out)
            .parse_inner(stream)
    }
}

/// See [`Parser::repeated`] and [`Parser::repeated_at_least`].
#[derive(Copy, Clone)]
pub struct Repeated<A>(pub(crate) A, pub(crate) usize);

impl<I: Clone, O, A: Parser<I, O, Error = E>, E: Error<Token = I>> Parser<I, Vec<O>> for Repeated<A> {
    type Error = E;

    fn parse_inner(&self, stream: &mut Stream<I>) -> PResult<Vec<O>, Self::Error> {
        let mut errors = Vec::new();
        let mut outputs = Vec::new();
        let mut alt = None;
        let mut old_offset = None;

        loop {
            if let ControlFlow::Break(b) = stream.attempt(|stream| match self.0.parse_inner(stream) {
                (mut a_errors, Ok((a_out, a_alt))) => {
                    (&mut errors).append(&mut a_errors);
                    alt = merge_alts(alt.take(), a_alt);
                    outputs.push(a_out);

                    if old_offset == Some(stream.offset()) {
                        panic!("Repeated parser iteration succeeded but consumed no tokens (i.e: continuing \
                            iteration would likely lead to an infinite loop, if the parser is pure). This is \
                            likely indicative of a parser bug. Consider using a more specific error recovery \
                            strategy.");
                    } else {
                        old_offset = Some(stream.offset());
                    }

                    (true, ControlFlow::Continue(()))
                },
                (mut a_errors, Err(a_err)) if outputs.len() < self.1 => {
                    (&mut errors).append(&mut a_errors);
                    (false, ControlFlow::Break((
                        std::mem::take(&mut errors),
                        Err(a_err),
                    )))
                },
                (a_errors, a_out) => {
                    // Find furthest alternative error
                    // TODO: Handle multiple alternative errors
                    // println!("Errors = {:?}, a_err = {:?}, a_errors = {:?}", errors, a_out.as_ref().err(), a_errors);
                    let alt = a_out.err().or(a_errors.into_iter().next()).or(alt.take());
                    // println!("alt = {:?}", alt);
                    (false, ControlFlow::Break((
                        std::mem::take(&mut errors),
                        Ok((std::mem::take(&mut outputs), alt)),
                    )))
                },
            }) {
                break b;
            }
        }
    }
}

/// See [`Parser::separated_by`].
pub struct SeparatedBy<A, B, U>(pub(crate) A, pub(crate) B, pub(crate) usize, pub(crate) bool, pub(crate) PhantomData<U>);

impl<A: Copy, B: Copy, U> Copy for SeparatedBy<A, B, U> {}
impl<A: Clone, B: Clone, U> Clone for SeparatedBy<A, B, U> {
    fn clone(&self) -> Self { Self(self.0.clone(), self.1.clone(), self.2, self.3, PhantomData) }
}

impl<I: Clone, O, U, A: Parser<I, O, Error = E>, B: Parser<I, U, Error = E>, E: Error<Token = I>> Parser<I, Vec<O>> for SeparatedBy<A, B, U> {
    type Error = E;

    fn parse_inner(&self, stream: &mut Stream<I>) -> PResult<Vec<O>, Self::Error> {
        (&self.0)
            .then((&self.1)
                .ignore_then(&self.0)
                .repeated()
                .then_ignore((&self.1).or_not()))
            .map(|(head, tail)| std::iter::once(head).chain(tail.into_iter()).collect())
            .parse_inner(stream)
    }
}

/// See [`Parser::map`].
pub struct Map<A, F, O>(pub(crate) A, pub(crate) F, pub(crate) PhantomData<O>);

impl<A: Copy, F: Copy, O> Copy for Map<A, F, O> {}
impl<A: Clone, F: Clone, O> Clone for Map<A, F, O> {
    fn clone(&self) -> Self { Self(self.0.clone(), self.1.clone(), PhantomData) }
}

impl<I: Clone, O, A: Parser<I, O, Error = E>, U, F: Fn(O) -> U, E: Error<Token = I>> Parser<I, U> for Map<A, F, O> {
    type Error = E;

    fn parse_inner(&self, stream: &mut Stream<I>) -> PResult<U, Self::Error> {
        let (errors, res) = self.0.parse_inner(stream);

        (errors, res.map(|(out, alt)| ((&self.1)(out), alt)))
    }
}

/// See [`Parser::map_with_span`].
pub struct MapWithSpan<A, F, O>(pub(crate) A, pub(crate) F, pub(crate) PhantomData<O>);

impl<A: Copy, F: Copy, O> Copy for MapWithSpan<A, F, O> {}
impl<A: Clone, F: Clone, O> Clone for MapWithSpan<A, F, O> {
    fn clone(&self) -> Self { Self(self.0.clone(), self.1.clone(), PhantomData) }
}

impl<I: Clone, O, A: Parser<I, O, Error = E>, U, F: Fn(O, Option<E::Span>) -> U, E: Error<Token = I>> Parser<I, U> for MapWithSpan<A, F, O> {
    type Error = E;

    fn parse_inner(&self, stream: &mut Stream<I>) -> PResult<U, Self::Error> {
        let (errors, res) = self.0.parse_inner(stream);

        let span = todo!();

        (errors, res.map(|(out, alt)| ((self.1)(out, span), alt)))
    }
}

/// See [`Parser::foldl`].
pub struct Foldl<A, F, O, U>(pub(crate) A, pub(crate) F, pub(crate) PhantomData<(O, U)>);

impl<A: Copy, F: Copy, O, U> Copy for Foldl<A, F, O, U> {}
impl<A: Clone, F: Clone, O, U> Clone for Foldl<A, F, O, U> {
    fn clone(&self) -> Self { Self(self.0.clone(), self.1.clone(), PhantomData) }
}

impl<I: Clone, O, A: Parser<I, (O, Vec<U>), Error = E>, U, F: Fn(O, U) -> O, E: Error<Token = I>> Parser<I, O> for Foldl<A, F, O, U> {
    type Error = E;

    fn parse_inner(&self, stream: &mut Stream<I>) -> PResult<O, Self::Error> {
        (&self.0).map(|(head, tail)| tail.into_iter().fold(head, &self.1))
            .parse_inner(stream)
    }
}

/// See [`Parser::foldr`].
pub struct Foldr<A, F, O, U>(pub(crate) A, pub(crate) F, pub(crate) PhantomData<(O, U)>);

impl<A: Copy, F: Copy, O, U> Copy for Foldr<A, F, O, U> {}
impl<A: Clone, F: Clone, O, U> Clone for Foldr<A, F, O, U> {
    fn clone(&self) -> Self { Self(self.0.clone(), self.1.clone(), PhantomData) }
}

impl<I: Clone, O, A: Parser<I, (Vec<O>, U), Error = E>, U, F: Fn(O, U) -> U, E: Error<Token = I>> Parser<I, U> for Foldr<A, F, O, U> {
    type Error = E;

    fn parse_inner(&self, stream: &mut Stream<I>) -> PResult<U, Self::Error> {
        (&self.0).map(|(init, end)| init.into_iter().rev().fold(end, |b, a| (&self.1)(a, b)))
            .parse_inner(stream)
    }
}

/// See [`Parser::map_err`].
#[derive(Copy, Clone)]
pub struct MapErr<A, F>(pub(crate) A, pub(crate) F);

impl<I: Clone, O, A: Parser<I, O, Error = E>, F: Fn(E) -> E, E: Error<Token = I>> Parser<I, O> for MapErr<A, F> {
    type Error = E;

    fn parse_inner(&self, stream: &mut Stream<I>) -> PResult<O, E> {
        let (errors, res) = self.0.parse_inner(stream);
        let mapper = |e: Located<E>| e.map(&self.1);
        (errors.into_iter().map(mapper).collect(), res.map(|(out, alt)| (out, alt.map(mapper))).map_err(mapper))
    }
}

/// See [`Parser::labelled`].
#[derive(Copy, Clone)]
pub struct Label<A, L>(pub(crate) A, pub(crate) L);

impl<I: Clone, O, A: Parser<I, O, Error = E>, L: Into<E::Pattern> + Clone, E: Error<Token = I>> Parser<I, O> for Label<A, L> {
    type Error = E;

    fn parse_inner(&self, stream: &mut Stream<I>) -> PResult<O, E> {
        (&self.0).map_err(|e| e.into_labelled(self.1.clone()))
            .parse_inner(stream)
    }
}

/// See [`Parser::to`].
pub struct To<A, O, U>(pub(crate) A, pub(crate) U, pub(crate) PhantomData<O>);

impl<A: Copy, U: Copy, O> Copy for To<A, O, U> {}
impl<A: Clone, U: Clone, O> Clone for To<A, O, U> {
    fn clone(&self) -> Self { Self(self.0.clone(), self.1.clone(), PhantomData) }
}

impl<I: Clone, O, A: Parser<I, O, Error = E>, U: Clone, E: Error<Token = I>> Parser<I, U> for To<A, O, U> {
    type Error = E;

    fn parse_inner(&self, stream: &mut Stream<I>) -> PResult<U, E> {
        (&self.0).map(|_| self.1.clone())
            .parse_inner(stream)
    }
}
