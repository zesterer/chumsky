use core::marker::PhantomData;

use super::{
    error::Error,
    input::{Input, InputRef, SliceInput},
    internal::{Check, Emit, Mode},
    Located, PResult, Parser,
};

pub struct RepeatedSlice<A, I: ?Sized, E = (), S = ()> {
    pub(crate) parser: A,
    pub(crate) at_least: usize,
    pub(crate) at_most: Option<usize>,
    pub(crate) phantom: PhantomData<(E, S, I)>,
}

impl<A: Copy, I: ?Sized, E, S> Copy for RepeatedSlice<A, I, E, S> {}
impl<A: Clone, I: ?Sized, E, S> Clone for RepeatedSlice<A, I, E, S> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            at_least: self.at_least,
            at_most: self.at_most,
            phantom: PhantomData,
        }
    }
}

impl<'a, A: Parser<'a, I, E, S>, I: Input + ?Sized, E: Error<I>, S: 'a> RepeatedSlice<A, I, E, S> {
    pub fn at_least(self, at_least: usize) -> Self {
        Self { at_least, ..self }
    }

    pub fn at_most(self, at_most: usize) -> Self {
        Self {
            at_most: Some(at_most),
            ..self
        }
    }

    pub fn exactly(self, exactly: usize) -> Self {
        Self {
            at_least: exactly,
            at_most: Some(exactly),
            ..self
        }
    }

    pub fn collect(self) -> Self
    where
        A: Parser<'a, I, E, S>,
    {
        Self {
            parser: self.parser,
            at_least: self.at_least,
            at_most: self.at_most,
            phantom: PhantomData,
        }
    }
}

impl<'a, A, I, E, S> Parser<'a, I, E, S> for RepeatedSlice<A, I, E, S>
where
    A: Parser<'a, I, E, S>,
    I: SliceInput + ?Sized,
    <I as SliceInput>::Slice: 'a,
    E: Error<I>,
    S: 'a,
{
    type Output = &'a <I as SliceInput>::Slice;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E> {
        let mut count = 0;
        let start = inp.save();
        loop {
            let before = inp.save();
            match self.parser.go::<M>(inp) {
                Ok(_) => {
                    count += 1;
                    if let Some(at_most) = self.at_most {
                        if count >= at_most {
                            let now = inp.save();
                            break Ok(M::bind(|| inp.slice(start..now)));
                        }
                    }
                }
                Err(e) => {
                    inp.rewind(before);
                    break if count >= self.at_least {
                        let now = inp.save();
                        break Ok(M::bind(|| inp.slice(start..now)));
                    } else {
                        Err(e)
                    };
                }
            }
        }
    }

    go_extra!();
}
