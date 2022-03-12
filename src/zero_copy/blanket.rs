use super::*;

impl<'a, T, I, E, S> Parser<'a, I, E, S> for &'a T
where
    T: Parser<'a, I, E, S>,
    I: Input + ?Sized,
    E: Error<I::Token>,
    S: 'a,
{
    type Output = T::Output;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E>
    where
        Self: Sized,
    {
        (*self).go::<M>(inp)
    }

    go_extra!();
}
