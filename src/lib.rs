#![feature(once_cell)]

pub mod text;
pub mod stream;

use crate::{
    stream::{Stream, IterStream},
};

use std::{
    iter::Peekable,
    marker::PhantomData,
    rc::Rc,
    lazy::OnceCell,
};

/*
fn or_zip_with<T, F: FnOnce(T, T) -> T>(a: Option<T>, b: Option<T>, f: F) -> Option<T> {
    match (a, b) {
        (Some(a), Some(b)) => Some(f(a, b)),
        (a, b) => a.or(b),
    }
}
*/

fn zip_or<T, F: FnOnce(T, T) -> T>(a: Option<T>, b: T, f: F) -> T {
    match a {
        Some(a) => f(a, b),
        None => b,
    }
}

#[derive(Debug)]
pub enum Error<I> {
    ExpectedFound(usize, Vec<I>, Option<I>),
}

impl<I> Error<I> {
    fn position(&self) -> usize {
        match self {
            Error::ExpectedFound(p, _, _) => *p,
        }
    }

    fn merge(self, other: Self) -> Self {
        if self.position() > other.position() {
            self
        } else if self.position() < other.position() {
            other
        } else {
            match (self, other) {
                (Error::ExpectedFound(p, mut e0, f0), Error::ExpectedFound(_, mut e1, f1)) => {
                    e0.append(&mut e1);
                    Error::ExpectedFound(p, e0, f0.or(f1))
                },
            }
        }
    }
}

pub trait Parser<I, O> {
    fn parse_inner<S: Stream<I>>(&self, stream: &mut S, errors: &mut Vec<Error<I>>) -> (usize, Result<O, Error<I>>) where Self: Sized;

    fn parse_recovery<Iter: Iterator<Item=I>>(&self, iter: Iter) -> (Option<O>, Vec<Error<I>>) where Self: Sized {
        let mut errors = Vec::new();
        match self.parse_inner(&mut IterStream::new(iter), &mut errors).1 {
            Ok(o) => (Some(o), errors),
            Err(e) => {
                errors.push(e);
                (None, errors)
            },
        }
    }
    fn parse<Iter: Iterator<Item=I>>(&self, iter: Iter) -> Result<O, Vec<Error<I>>> where Self: Sized {
        let (output, errors) = self.parse_recovery(iter);
        if errors.len() > 0 {
            Err(errors)
        } else {
            Ok(output.expect("Parsing failed, but no errors were emitted. This troubling, to say the least."))
        }
    }

    fn map<U, F: Fn(O) -> U>(self, f: F) -> Map<Self, F, O> where Self: Sized { Map(self, f, PhantomData) }
    fn to<U: Clone>(self, x: U) -> To<Self, O, U> where Self: Sized { To(self, x, PhantomData) }
    fn ignored(self) -> Ignored<Self, O> where Self: Sized { To(self, (), PhantomData) }

    fn then<U, P: Parser<I, U>>(self, other: P) -> Then<Self, P> where Self: Sized { Then(self, other) }
    fn padding_for<U, P: Parser<I, U>>(self, other: P) -> Map<Then<Self, P>, fn((O, U)) -> U, (O, U)> where Self: Sized { Map(Then(self, other), |(_, u)| u, PhantomData) }
    fn padded_by<U, P: Parser<I, U>>(self, other: P) -> Map<Then<Self, P>, fn((O, U)) -> O, (O, U)> where Self: Sized { Map(Then(self, other), |(o, _)| o, PhantomData) }
    // fn then_catch(self, end: I) -> ThenCatch<Self, I> where Self: Sized { ThenCatch(self, end) }
    fn delimited_by(self, start: I, end: I) -> DelimitedBy<Self, I> where Self: Sized { DelimitedBy(self, start, end) }

    fn or<P: Parser<I, O>>(self, other: P) -> Or<Self, P> where Self: Sized { Or(self, other) }
    fn repeated(self) -> Repeated<Self> where Self: Sized { Repeated(self) }
}

pub type Ignored<P, O> = To<P, O, ()>;

#[derive(Clone)]
pub struct Just<I>(I);

impl<I: Clone + PartialEq> Parser<I, I> for Just<I> {
    fn parse_inner<S: Stream<I>>(&self, stream: &mut S, _: &mut Vec<Error<I>>) -> (usize, Result<I, Error<I>>) where Self: Sized {
        match stream.peek() {
            Some(x) if x == &self.0 => (1, Ok(stream.next().unwrap())),
            x => {
                let x = x.cloned();
                (0, Err(Error::ExpectedFound(stream.position(), vec![self.0.clone()], x)))
            },
        }
    }
}

pub fn just<I: Clone + PartialEq>(x: I) -> Just<I> {
    Just(x)
}

#[derive(Clone)]
pub struct Matches<F>(F);

impl<I: Clone, F: Fn(&I) -> bool> Parser<I, I> for Matches<F> {
    fn parse_inner<S: Stream<I>>(&self, stream: &mut S, _: &mut Vec<Error<I>>) -> (usize, Result<I, Error<I>>) where Self: Sized {
        match stream.peek() {
            Some(x) if (self.0)(x) => (1, Ok(stream.next().unwrap())),
            x => {
                let x = x.cloned();
                (0, Err(Error::ExpectedFound(stream.position(), Vec::new(), x)))
            },
        }
    }
}

pub fn matches<I, F: Fn(&I) -> bool>(f: F) -> Matches<F> {
    Matches(f)
}

#[derive(Clone)]
pub struct Or<A, B>(A, B);

impl<I: Clone, O, A: Parser<I, O>, B: Parser<I, O>> Parser<I, O> for Or<A, B> {
    fn parse_inner<S: Stream<I>>(&self, stream: &mut S, errors: &mut Vec<Error<I>>) -> (usize, Result<O, Error<I>>) where Self: Sized {
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

#[derive(Clone)]
pub struct Then<A, B>(A, B);

impl<I, O, U, A: Parser<I, O>, B: Parser<I, U>> Parser<I, (O, U)> for Then<A, B> {
    fn parse_inner<S: Stream<I>>(&self, stream: &mut S, errors: &mut Vec<Error<I>>) -> (usize, Result<(O, U), Error<I>>) where Self: Sized {
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
#[derive(Clone)]
pub struct ThenCatch<A, I>(A, I);

impl<I: Clone + PartialEq, O, A: Parser<I, O>> Parser<I, Option<O>> for ThenCatch<A, I> {
    fn parse_inner<S: Stream<I>>(&self, stream: &mut S, errors: &mut Vec<Error<I>>) -> (usize, Result<Option<O>, Error<I>>) where Self: Sized {
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
                Some(x) => res = Err(zip_or(res.err(), Error::ExpectedFound(stream.position(), vec![self.1.clone()], Some(x)), |a, b| a.merge(b))),
                None => break (n, Err(zip_or(res.err(), Error::ExpectedFound(stream.position(), vec![self.1.clone()], None), |a, b| a.merge(b)))),
            }
        }
    }
}
*/

#[derive(Clone)]
pub struct DelimitedBy<A, I>(A, I, I);

impl<I: Clone + PartialEq, O, A: Parser<I, O>> Parser<I, Option<O>> for DelimitedBy<A, I> {
    fn parse_inner<S: Stream<I>>(&self, stream: &mut S, errors: &mut Vec<Error<I>>) -> (usize, Result<Option<O>, Error<I>>) where Self: Sized {
        let mut n = match stream.peek() {
            Some(x) if x == &self.1 => { stream.next(); 1 },
            x => {
                let x = x.cloned();
                return (0, Err(Error::ExpectedFound(stream.position(), vec![self.1.clone()], x)))
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
                Some(x) => res = Err(zip_or(res.err(), Error::ExpectedFound(stream.position(), vec![self.1.clone()], Some(x)), |a, b| a.merge(b))),
                None => break (n, Err(zip_or(res.err(), Error::ExpectedFound(stream.position(), vec![self.1.clone()], None), |a, b| a.merge(b))))
            }
        }
    }
}

#[derive(Clone)]
pub struct Repeated<A>(A);

impl<I, O, A: Parser<I, O>> Parser<I, Vec<O>> for Repeated<A> {
    fn parse_inner<S: Stream<I>>(&self, stream: &mut S, errors: &mut Vec<Error<I>>) -> (usize, Result<Vec<O>, Error<I>>) where Self: Sized {
        let mut outputs = Vec::new();

        let mut n = 0;
        loop {
            match self.0.parse_inner(stream, errors) {
                (m, Ok(o)) => {
                    outputs.push(o);
                    n += m;
                },
                (0, Err(_)) => break (n, Ok(outputs)),
                (m, Err(e)) => break (n + m, Err(e)),
            }
        }
    }
}

pub struct Map<A, F, O>(A, F, PhantomData<O>);

impl<A: Clone, F: Clone, O> Clone for Map<A, F, O> {
    fn clone(&self) -> Self { Self(self.0.clone(), self.1.clone(), PhantomData) }
}

impl<I, O, A: Parser<I, O>, U, F: Fn(O) -> U> Parser<I, U> for Map<A, F, O> {
    fn parse_inner<S: Stream<I>>(&self, stream: &mut S, errors: &mut Vec<Error<I>>) -> (usize, Result<U, Error<I>>) where Self: Sized {
        let (n, res) = self.0.parse_inner(stream, errors);
        (n, res.map(&self.1))
    }
}

pub struct To<A, O, U>(A, U, PhantomData<O>);

impl<A: Clone, U: Clone, O> Clone for To<A, O, U> {
    fn clone(&self) -> Self { Self(self.0.clone(), self.1.clone(), PhantomData) }
}

impl<I, O, A: Parser<I, O>, U: Clone> Parser<I, U> for To<A, O, U> {
    fn parse_inner<S: Stream<I>>(&self, stream: &mut S, errors: &mut Vec<Error<I>>) -> (usize, Result<U, Error<I>>) where Self: Sized {
        let (n, res) = self.0.parse_inner(stream, errors);
        (n, res.map(|_| self.1.clone()))
    }
}

type ParserFn<'a, I, O> = dyn Fn(&mut dyn Stream<I>, &mut Vec<Error<I>>) -> (usize, Result<O, Error<I>>) + 'a;

pub struct Recursive<'a, I, O>(Rc<OnceCell<Box<ParserFn<'a, I, O>>>>);

impl<'a, I, O> Parser<I, O> for Recursive<'a, I, O> {
    fn parse_inner<S: Stream<I>>(&self, stream: &mut S, errors: &mut Vec<Error<I>>) -> (usize, Result<O, Error<I>>) where Self: Sized {
        (self.0
            .get()
            .expect("Recursive parser used prior to construction"))(stream, errors)
    }
}

pub fn recursive<'a, I, O, P: Parser<I, O> + 'a, F: FnOnce(Recursive<'a, I, O>) -> P>(f: F) -> Recursive<'a, I, O> {
    let rc = Rc::new(OnceCell::new());
    let parser = f(Recursive(rc.clone()));
    rc.set(Box::new(move |mut stream: &mut dyn Stream<I>, errors| parser.parse_inner(&mut stream, errors)))
        .unwrap_or_else(|_| unreachable!());
    Recursive(rc)
}
