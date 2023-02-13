//! TODO

use super::*;

mod internal {
    use super::*;

    pub trait ExtraSealed {}
    impl<E, S, C> ExtraSealed for Full<E, S, C> {}
}

use internal::ExtraSealed;

type DefaultErr = EmptyErr;
type DefaultState = ();
type DefaultCtx = ();

/// Sealed trait for parser extra information - error type, state type, etc.
pub trait ParserExtra<'a, I>: 'a + ExtraSealed
where
    I: ?Sized + Input,
{
    /// Error type to use for the parser
    type Error: Error<I> + 'a;
    /// State type to use for the parser
    type State: 'a;
    /// Context used for parser configuration
    type Context: 'a;
}

/// Use all default extra types
pub type Default = Full<DefaultErr, DefaultState, DefaultCtx>;

/// Use specified error type, but default other types
pub type Err<E> = Full<E, DefaultState, DefaultCtx>;

/// Use specified state type, but default other types
pub type State<S> = Full<DefaultErr, S, DefaultCtx>;

/// Use specified context type, but default other types
pub type Context<C> = Full<DefaultErr, DefaultState, C>;

/// Specify all extra types
pub struct Full<E, S, C>(PhantomData<(E, S, C)>);

impl<'a, I, E, S, C> ParserExtra<'a, I> for Full<E, S, C>
where
    I: ?Sized + Input,
    E: Error<I> + 'a,
    S: 'a,
    C: 'a,
{
    type Error = E;
    type State = S;
    type Context = C;
}
