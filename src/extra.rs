//! Generic error, state and context types for parsers
//! Useful for custom allocation, error handling, context-specific parsers, and more.

use super::*;

type DefaultErr = EmptyErr;
type DefaultState = ();
type DefaultCtx = ();

/// Sealed trait for parser extra information - error type, state type, etc.
pub trait ParserExtra<'a, I>: 'a + Sealed
where
    I: Input<'a>,
{
    /// Error type to use for the parser.
    type Error: Error<'a, I> + 'a;
    /// State type to use for the parser.
    type State: 'a;
    /// Context used for parser configuration.
    type Context: 'a;
}

/// Use all default extra types
pub type Default = Full<DefaultErr, DefaultState, DefaultCtx>;

/// Use specified error type, but default other types
pub type Err<E> = Full<E, DefaultState, DefaultCtx>;

/// Use specified state type, but default other types
///
/// Use `State<S>` or `Full<E, S, C>` as the `E` type parameter of a parser to use a custom state type.
/// You can then use `parser().parse_with_state(&mut S)` to parse with a custom state
///
/// # Examples
///
/// One common use case for this is arena allocation of AST Nodes or tokens.
///
/// ```
/// // Use a slotmap to allocate AST nodes, returning an id from each parser instead of a node
/// pub fn parser<'src>() -> impl Parser<'src, BoxedStream<'src, Token>, NodeId, State<SlotMap<NodeId, ASTNode>> {
///     // ...
/// }
/// ```
///
pub type State<S> = Full<DefaultErr, S, DefaultCtx>;

/// Use specified context type, but default other types
pub type Context<C> = Full<DefaultErr, DefaultState, C>;

/// Specify all extra types
pub struct Full<E, S, C>(PhantomData<(E, S, C)>);

impl<E, S, C> Sealed for Full<E, S, C> {}
impl<'a, I, E, S, C> ParserExtra<'a, I> for Full<E, S, C>
where
    I: Input<'a>,
    E: Error<'a, I> + 'a,
    S: 'a,
    C: 'a,
{
    type Error = E;
    type State = S;
    type Context = C;
}
