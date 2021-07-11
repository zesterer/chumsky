use super::*;

type ParserFn<'a, I, O, E> = dyn Fn(&mut dyn Stream<I>, &mut Vec<E>) -> (usize, Result<O, E>) + 'a;

/// See [`recursive()`].
pub struct Recursive<'a, I, O, E>(Rc<OnceCell<Box<ParserFn<'a, I, O, E>>>>);

impl<'a, I, O, E: Error<I>> Parser<I, O> for Recursive<'a, I, O, E> {
    type Error = E;

    fn parse_inner<S: Stream<I>>(&self, stream: &mut S, errors: &mut Vec<Self::Error>) -> (usize, Result<O, E>) where Self: Sized {
        (self.0
            .get()
            .expect("Recursive parser used prior to construction"))(stream, errors)
    }
}

/// Construct a recursive parser (i.e: a parser that may contain itself as part of its pattern).
///
/// The given function must create the parser. The parser must not be used to parse input before this function returns.
pub fn recursive<'a, I, O, P: Parser<I, O, Error = E> + 'a, F: FnOnce(Recursive<'a, I, O, E>) -> P, E: Error<I>>(f: F) -> Recursive<'a, I, O, E> {
    let rc = Rc::new(OnceCell::new());
    let parser = f(Recursive(rc.clone()));
    rc.set(Box::new(move |mut stream: &mut dyn Stream<I>, errors| parser.parse_inner(&mut stream, errors)))
        .unwrap_or_else(|_| unreachable!());
    Recursive(rc)
}
