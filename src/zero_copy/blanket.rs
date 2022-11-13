use super::*;

impl<'a, T, I, O, E, S> Parser<'a, I, O, E, S> for &'a T
where
    T: Parser<'a, I, O, E, S>,
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, O, E>
    where
        Self: Sized,
    {
        (*self).go::<M>(inp)
    }

    go_extra!(O);
}
