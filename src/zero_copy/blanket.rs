use super::*;

impl<'a, T, I, O, E> Parser<'a, I, O, E> for &'a T
where
    T: Parser<'a, I, O, E>,
    I: Input + ?Sized,
    E: ParserExtra<'a, I>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O, E::Error>
    where
        Self: Sized,
    {
        (*self).go::<M>(inp)
    }

    go_extra!(O);
}
