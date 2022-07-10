use super::*;

enum RecursiveInner<T> {
    Owned(Rc<T>),
    Unowned(Weak<T>),
}

type OnceParser<'a, I, O, E, S> = OnceCell<Box<dyn Parser<'a, I, E, S, Output = O> + 'a>>;

pub struct Recursive<'a, I: ?Sized, O, E, S = ()> {
    inner: RecursiveInner<OnceParser<'a, I, O, E, S>>,
}

impl<'a, I: Input + ?Sized, O, E: Error<I>, S> Recursive<'a, I, O, E, S> {
    fn cell(&self) -> Rc<OnceParser<'a, I, O, E, S>> {
        match &self.inner {
            RecursiveInner::Owned(x) => x.clone(),
            RecursiveInner::Unowned(x) => x
                .upgrade()
                .expect("Recursive parser used before being defined"),
        }
    }

    pub fn declare() -> Self {
        Recursive {
            inner: RecursiveInner::Owned(Rc::new(OnceCell::new())),
        }
    }

    pub fn define<P: Parser<'a, I, E, S, Output = O> + 'a>(&mut self, parser: P) {
        self.cell()
            .set(Box::new(parser))
            .unwrap_or_else(|_| panic!("recursive parser already declared"));
    }
}

impl<'a, I: ?Sized, O, E, S> Clone for Recursive<'a, I, O, E, S> {
    fn clone(&self) -> Self {
        Self {
            inner: match &self.inner {
                RecursiveInner::Owned(x) => RecursiveInner::Owned(x.clone()),
                RecursiveInner::Unowned(x) => RecursiveInner::Unowned(x.clone()),
            },
        }
    }
}

impl<'a, I, E, S, O> Parser<'a, I, E, S> for Recursive<'a, I, O, E, S>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
{
    type Output = O;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E> {
        M::invoke(
            self.cell()
                .get()
                .expect("Recursive parser used before being defined")
                .as_ref(),
            inp,
        )
    }

    go_extra!();
}

pub fn recursive<
    'a,
    I: Input + ?Sized,
    E: Error<I>,
    S,
    A: Parser<'a, I, E, S> + 'a,
    F: FnOnce(Recursive<'a, I, A::Output, E, S>) -> A,
>(
    f: F,
) -> Recursive<'a, I, A::Output, E, S> {
    let mut recursive = Recursive::declare();
    recursive.define(f(Recursive {
        inner: match &recursive.inner {
            RecursiveInner::Owned(x) => RecursiveInner::Unowned(Rc::downgrade(x)),
            RecursiveInner::Unowned(_) => unreachable!(),
        },
    }));
    recursive
}
