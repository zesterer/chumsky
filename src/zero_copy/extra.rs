//! TODO

use super::*;

mod internal {
    use super::*;

    pub trait ExtraSealed {}

    impl ExtraSealed for ExtraDefault {}
    impl<E> ExtraSealed for Err<E> {}
    impl<S> ExtraSealed for State<S> {}
    impl<E, S> ExtraSealed for Full<E, S> {}
}

use internal::ExtraSealed;

/// TODO
pub trait ParserExtra<'a, I>: 'a + ExtraSealed
where
    I: ?Sized + Input,
{
    /// TODO
    type Error: Error<I> + 'a;
    /// TODO
    type State: 'a;
}

/// TODO
pub struct ExtraDefault;

impl<'a, I> ParserExtra<'a, I> for ExtraDefault
where
    I: ?Sized + Input,
{
    type Error = EmptyErr;
    type State = ();
}

/// TODO
pub struct Err<E>(PhantomData<E>);

impl<'a, I, E> ParserExtra<'a, I> for Err<E>
where
    I: ?Sized + Input,
    E: Error<I> + 'a,
{
    type Error = E;
    type State = ();
}

/// TODO
pub struct State<S>(PhantomData<S>);

impl<'a, I, S> ParserExtra<'a, I> for State<S>
where
    I: ?Sized + Input,
    S: 'a,
{
    type Error = EmptyErr;
    type State = S;
}

/// TODO
pub struct Full<E, S>(PhantomData<(E, S)>);

impl<'a, I, E, S> ParserExtra<'a, I> for Full<E, S>
where
    I: ?Sized + Input,
    E: Error<I> + 'a,
    S: 'a,
{
    type Error = E;
    type State = S;
}
