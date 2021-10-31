use super::*;

use std::rc::Rc;

// TODO: Remove when `OnceCell` is stable
struct OnceCell<T>(std::cell::RefCell<Option<T>>);
impl<T> OnceCell<T> {
    pub fn new() -> Self { Self(std::cell::RefCell::new(None)) }
    pub fn set(&self, x: T) -> Result<(), ()> {
        *self.0.try_borrow_mut().map_err(|_| ())? = Some(x);
        Ok(())
    }
    pub fn get(&self) -> Option<std::cell::Ref<T>> { Some(std::cell::Ref::map(self.0.borrow(), |x| x.as_ref().unwrap())) }
}

/// See [`recursive()`].
pub struct Recursive<'a, I, O, E: Error<I>>(Rc<OnceCell<Box<dyn Parser<I, O, Error = E> + 'a>>>);

impl<'a, I: Clone, O, E: Error<I>> Clone for Recursive<'a, I, O, E> {
    fn clone(&self) -> Self { Self(self.0.clone()) }
}

impl<'a, I: Clone, O, E: Error<I>> Parser<I, O> for Recursive<'a, I, O, E> {
    type Error = E;

    fn parse_inner<D: Debugger>(&self, debugger: &mut D, stream: &mut StreamOf<I, Self::Error>) -> PResult<I, O, Self::Error> {
        #[allow(deprecated)]
        debugger.invoke(self.0.get().expect("Recursive parser used prior to construction").as_ref(), stream)
    }

    fn parse_inner_verbose(&self, d: &mut Verbose, s: &mut StreamOf<I, E>) -> PResult<I, O, E> { #[allow(deprecated)] self.parse_inner(d, s) }
    fn parse_inner_silent(&self, d: &mut Silent, s: &mut StreamOf<I, E>) -> PResult<I, O, E> { #[allow(deprecated)] self.parse_inner(d, s) }
}

/// Construct a recursive parser (i.e: a parser that may contain itself as part of its pattern).
///
/// The given function must create the parser. The parser must not be used to parse input before this function returns.
///
/// # Examples
///
/// ```
/// # use chumsky::prelude::*;
/// #[derive(Debug, PartialEq)]
/// enum Tree {
///     Leaf(String),
///     Branch(Vec<Tree>),
/// }
///
/// // Parser that recursively parses nested lists
/// let tree = recursive::<_, _, _, _, Simple<char>>(|tree| tree
///     .separated_by(just(','))
///     .delimited_by('[', ']')
///     .map(Tree::Branch)
///     .or(text::ident().map(Tree::Leaf))
///     .padded());
///
/// assert_eq!(tree.parse("hello"), Ok(Tree::Leaf("hello".to_string())));
/// assert_eq!(tree.parse("[a, b, c]"), Ok(Tree::Branch(vec![
///     Tree::Leaf("a".to_string()),
///     Tree::Leaf("b".to_string()),
///     Tree::Leaf("c".to_string()),
/// ])));
/// // The parser can deal with arbitrarily complex nested lists
/// assert_eq!(tree.parse("[[a, b], c, [d, [e, f]]]"), Ok(Tree::Branch(vec![
///     Tree::Branch(vec![
///         Tree::Leaf("a".to_string()),
///         Tree::Leaf("b".to_string()),
///     ]),
///     Tree::Leaf("c".to_string()),
///     Tree::Branch(vec![
///         Tree::Leaf("d".to_string()),
///         Tree::Branch(vec![
///             Tree::Leaf("e".to_string()),
///             Tree::Leaf("f".to_string()),
///         ]),
///     ]),
/// ])));
/// ```
pub fn recursive<'a, I: Clone, O, P: Parser<I, O, Error = E> + 'a, F: FnOnce(Recursive<'a, I, O, E>) -> P, E: Error<I>>(f: F) -> Recursive<'a, I, O, E> {
    let rc = Rc::new(OnceCell::new());
    let parser = f(Recursive(rc.clone()));
    rc.set(Box::new(parser))
        .unwrap_or_else(|_| unreachable!());
    Recursive(rc)
}
