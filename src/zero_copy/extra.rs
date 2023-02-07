//! TODO

use super::*;

mod internal {
    use super::*;

    pub trait ExtraSealed {}
    impl<E, S> ExtraSealed for Full<E, S> {}
}

use internal::ExtraSealed;

type DefaultErr = EmptyErr;
type DefaultState = ();

/// Sealed trait for parser extra information - error type, state type, etc.
pub trait ParserExtra<'a, I>: 'a + ExtraSealed
where
    I: ?Sized + Input,
{
    /// Error type to use for the parser
    type Error: Error<I> + 'a;
    /// State type to use for the parser
    type State: 'a;
}

/// Use all default extra types
pub type Default = Full<DefaultErr, DefaultState>;

/// Use specified error type, but default other types
pub type Err<E> = Full<E, DefaultState>;

/// Use specified state type, but default other types
pub type State<S> = Full<DefaultErr, S>;

/// Specify all extra types
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
