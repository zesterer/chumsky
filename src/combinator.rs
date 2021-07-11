use super::*;

/// See [`Parser::ignored`].
pub type Ignored<P, O> = To<P, O, ()>;

/// See [`Parser::padding_for`].
pub type PaddingFor<A, B, O, U> = Map<Then<A, B>, fn((O, U)) -> U, (O, U)>;

/// See [`Parser::padded_by`].
pub type PaddedBy<A, B, O, U> = Map<Then<A, B>, fn((O, U)) -> O, (O, U)>;

/// See [`Parser::foldl`].
// TODO: Don't use a `Box` here.
pub type Foldl<'a, P, A, B, O> = Map<P, Box<dyn Fn((A, Vec<B>)) -> A + 'a>, O>;

/// See [`Parser::foldr`].
// TODO: Don't use a `Box` here.
pub type Foldr<'a, P, A, B, O> = Map<P, Box<dyn Fn((Vec<A>, B)) -> B + 'a>, O>;

/// See [`Parser::or`].
#[derive(Copy, Clone)]
pub struct Or<A, B>(pub(crate) A, pub(crate) B);

impl<I: Clone, O, A: Parser<I, O, Error =  E>, B: Parser<I, O, Error = E>, E: Error<I>> Parser<I, O> for Or<A, B> {
    type Error = E;

    fn parse_inner<S: Stream<I>>(&self, stream: &mut S, errors: &mut Vec<Self::Error>) -> (usize, Result<O, E>) where Self: Sized {
        match self.0.parse_inner(stream, errors) {
            (n, Ok(o)) => (n, Ok(o)),
            (0, Err(e)) => match self.1.parse_inner(stream, errors) {
                (m, Ok(o)) => (m, Ok(o)),
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

    fn parse_inner<S: Stream<I>>(&self, stream: &mut S, errors: &mut Vec<Self::Error>) -> (usize, Result<Option<O>, E>) where Self: Sized {
        match self.0.parse_inner(stream, errors) {
            (n, Ok(o)) => (n, Ok(Some(o))),
            (0, Err(_)) => (0, Ok(None)),
            (n, Err(e)) => (n, Err(e)),
        }
    }
}

/// See [`Parser::then`].
#[derive(Copy, Clone)]
pub struct Then<A, B>(pub(crate) A, pub(crate) B);

impl<I, O, U, A: Parser<I, O, Error = E>, B: Parser<I, U, Error = E>, E: Error<I>> Parser<I, (O, U)> for Then<A, B> {
    type Error = E;

    fn parse_inner<S: Stream<I>>(&self, stream: &mut S, errors: &mut Vec<Self::Error>) -> (usize, Result<(O, U), E>) where Self: Sized {
        match self.0.parse_inner(stream, errors) {
            (n, Ok(o)) => match self.1.parse_inner(stream, errors) {
                (m, Ok(u)) => (n + m, Ok((o, u))),
                (m, Err(e)) => (n + m, Err(e)),
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

    fn parse_inner<S: Stream<I>>(&self, stream: &mut S, errors: &mut Vec<Self::Error>) -> (usize, Result<Option<O>, E>) where Self: Sized {
        let (mut n, mut res) = self.0.parse_inner(stream, errors);

        assert!(n > 0 /*|| res.is_ok()*/, "ThenCatch must consume input (i.e: be non-optional) to avoid consuming everything");

        loop {
            n += 1;
            match stream.next() {
                Some(x) if x == self.1 => match res {
                    Ok(o) => break (n, Ok(Some(o))),
                    Err(e) => {
                        errors.push(e);
                        break (n, Ok(None));
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

    fn parse_inner<S: Stream<I>>(&self, stream: &mut S, errors: &mut Vec<Self::Error>) -> (usize, Result<Option<O>, E>) where Self: Sized {
        let mut n = match stream.peek() {
            Some(x) if x == &self.1 => { stream.next(); 1 },
            x => {
                let x = x.cloned();
                return (0, Err(E::expected_found(stream.position(), vec![self.1.clone()], x)))
            },
        };

        let (m, mut res) = self.0.parse_inner(stream, errors);
        n += m;

        let mut balance = 0;
        loop {
            n += 1;
            match stream.next() {
                Some(x) if x == self.1 => balance -= 1,
                Some(x) if x == self.2 => if balance == 0 {
                    match res {
                        Ok(o) => break (n, Ok(Some(o))),
                        Err(e) => {
                            errors.push(e);
                            break (n, Ok(None));
                        },
                    }
                } else {
                    balance += 1;
                },
                Some(x) => res = Err(res.err().unwrap_or_else(|| E::expected_found(stream.position(), vec![self.2.clone()], Some(x)))),
                None => break (n, Err(res.err().unwrap_or_else(|| E::expected_found(stream.position(), vec![self.2.clone()], None)))),
            }
        }
    }
}

/// See [`Parser::repeated`] and [`Parser::repeated_at_least`].
#[derive(Copy, Clone)]
pub struct Repeated<A>(pub(crate) A, pub(crate) usize);

impl<I, O, A: Parser<I, O, Error = E>, E: Error<I>> Parser<I, Vec<O>> for Repeated<A> {
    type Error = E;

    fn parse_inner<S: Stream<I>>(&self, stream: &mut S, errors: &mut Vec<Self::Error>) -> (usize, Result<Vec<O>, E>) where Self: Sized {
        let mut outputs = Vec::new();

        let mut n = 0;
        loop {
            match self.0.parse_inner(stream, errors) {
                (m, Ok(o)) => {
                    outputs.push(o);
                    n += m;
                },
                (0, Err(_)) if outputs.len() >= self.1 => break (n, Ok(outputs)),
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

    fn parse_inner<S: Stream<I>>(&self, stream: &mut S, errors: &mut Vec<Self::Error>) -> (usize, Result<U, E>) where Self: Sized {
        let (n, res) = self.0.parse_inner(stream, errors);
        (n, res.map(&self.1))
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

    fn parse_inner<S: Stream<I>>(&self, stream: &mut S, errors: &mut Vec<Self::Error>) -> (usize, Result<U, E>) where Self: Sized {
        let (n, res) = self.0.parse_inner(stream, errors);
        (n, res.map(|_| self.1.clone()))
    }
}
