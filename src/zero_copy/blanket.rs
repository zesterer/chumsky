use super::*;

impl<'a, T, I, O, E> Parser<'a, I, O, E> for &'a T
where
    T: Parser<'a, I, O, E>,
    I: Input + ?Sized,
    E: ParserExtra<'a, I>,
{
    type Config = T::Config;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O, E::Error>
    where
        Self: Sized,
    {
        (*self).go::<M>(inp)
    }

    fn go_cfg<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>, cfg: Self::Config) -> PResult<M, O, E::Error>
    where
        Self: Sized,
    {
        (*self).go_cfg::<M>(inp, cfg)
    }

    go_extra!(O);
}
