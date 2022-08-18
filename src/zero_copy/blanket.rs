use super::*;

impl<'a, T, I, E, S> Parser<'a, I, E, S> for &'a T
where
    T: Parser<'a, I, E, S>,
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
{
    type Output = T::Output;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E>
    where
        Self: Sized,
    {
        (*self).go::<M>(inp)
    }

    #[cfg(debug_assertions)]
    fn details(&self) -> (&str, Location) { (*self).details() }

    #[cfg(debug_assertions)]
    fn fp(&self) -> Range<Option<usize>> { (*self).fp() }

    go_extra!();
}
