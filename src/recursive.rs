use super::*;

use std::rc::Rc;

// TODO: Remove when `OnceCell` is stable
struct OnceCell<T>(std::cell::RefCell<Option<T>>);

impl<T> OnceCell<T> {
    pub const fn new() -> Self {
        Self(std::cell::RefCell::new(None))
    }

    pub fn set(&self, x: T) -> Result<(), ()> {
        *self.0.try_borrow_mut().map_err(|_| ())? = Some(x);
        Ok(())
    }

    pub fn get(&self) -> Option<std::cell::Ref<T>> {
        Some(std::cell::Ref::map(self.0.borrow(), |x| {
            x.as_ref().unwrap()
        }))
    }
}

/// See [`recursive()`].
pub struct Recursive<'a, I, O, E: Error<I>>(Rc<OnceCell<Box<ParserFn<'a, I, O, E>>>>);

impl<'a, I, O, E: Error<I>> Clone for Recursive<'a, I, O, E> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<'a, I, O, E: Error<I>> Parser<I, O> for Recursive<'a, I, O, E> {
    type Error = E;

    fn parse_inner<S: Stream<I, <Self::Error as Error<I>>::Span>>(
        &self,
        stream: &mut S,
        errors: &mut Vec<Self::Error>,
    ) -> (usize, Result<(O, Option<E>), E>)
    where
        Self: Sized,
    {
        (self
            .0
            .get()
            .expect("Recursive parser used prior to construction"))(stream, errors)
    }
}

/// Construct a recursive parser (i.e: a parser that may contain itself as part of its pattern).
///
/// The given function must create the parser. The parser must not be used to parse input before this function returns.
pub fn recursive<
    'a,
    I,
    O,
    P: Parser<I, O, Error = E> + 'a,
    F: FnOnce(Recursive<'a, I, O, E>) -> P,
    E: Error<I>,
>(
    f: F,
) -> Recursive<'a, I, O, E> {
    let rc = Rc::new(OnceCell::new());
    let parser = f(Recursive(rc.clone()));
    rc.set(Box::new(
        move |mut stream: &mut dyn Stream<I, E::Span>, errors| {
            parser.parse_inner(&mut stream, errors)
        },
    ))
    .unwrap_or_else(|_| unreachable!());
    Recursive(rc)
}
