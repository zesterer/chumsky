use super::*;

impl<'a, T, In, Out, Err, State, Ctx> Parser<'a, In, Out, Err, State, Ctx> for &'a T
where
    T: Parser<'a, In, Out, Err, State, Ctx>,
    In: Input + ?Sized,
    Err: Error<In>,
    State: 'a,
{
    type Config = T::Config;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>) -> PResult<M, Out, Err>
    where
        Self: Sized,
    {
        (*self).go::<M>(inp)
    }

    fn go_cfg<M: Mode>(&self, inp: &mut InputRef<'a, '_, In, Err, State, Ctx>, cfg: Self::Config) -> PResult<M, Out, Err> where Self: Sized {
        (*self).go_cfg::<M>(inp, cfg)
    }

    go_extra!(Out);
}
