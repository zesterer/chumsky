use super::*;

enum RecursiveInner<T: ?Sized> {
    Owned(Rc<T>),
    Unowned(Weak<T>),
}

type OnceParser<'a, I, O, E, S> = OnceCell<Box<dyn Parser<'a, I, E, S, Output = O> + 'a>>;

pub type Direct<'a, I, O, E, S = ()> = dyn Parser<'a, I, E, S, Output = O> + 'a;

pub struct Indirect<'a, I: ?Sized, O, E, S = ()> {
    inner: OnceParser<'a, I, O, E, S>,
}

pub struct Recursive<P: ?Sized> {
    inner: RecursiveInner<P>,
    #[cfg(debug_assertions)] pub(crate) location: Location<'static>,
}

impl<'a, I: Input + ?Sized, O, E: Error<I>, S> Recursive<Indirect<'a, I, O, E, S>> {
    #[track_caller]
    pub fn declare() -> Self {
        Recursive {
            inner: RecursiveInner::Owned(Rc::new(Indirect {
                inner: OnceCell::new(),
            })),
            #[cfg(debug_assertions)] location: *Location::caller(),
        }
    }

    pub fn define<P: Parser<'a, I, E, S, Output = O> + 'a>(&mut self, parser: P) {
        self.parser()
            .inner
            .set(Box::new(parser))
            .unwrap_or_else(|_| panic!("recursive parser already declared"));
    }
}

impl<P: ?Sized> Recursive<P> {
    fn parser(&self) -> Rc<P> {
        match &self.inner {
            RecursiveInner::Owned(x) => x.clone(),
            RecursiveInner::Unowned(x) => x
                .upgrade()
                .expect("Recursive parser used before being defined"),
        }
    }
}

impl<P: ?Sized> Clone for Recursive<P> {
    fn clone(&self) -> Self {
        Self {
            inner: match &self.inner {
                RecursiveInner::Owned(x) => RecursiveInner::Owned(x.clone()),
                RecursiveInner::Unowned(x) => RecursiveInner::Unowned(x.clone()),
            },
            #[cfg(debug_assertions)] location: self.location,
        }
    }
}

impl<'a, I, E, S, O> Parser<'a, I, E, S> for Recursive<Indirect<'a, I, O, E, S>>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
{
    type Output = O;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E> {
        M::invoke(
            self.parser()
                .inner
                .get()
                .expect("Recursive parser used before being defined")
                .as_ref(),
            inp,
        )
    }

    #[cfg(debug_assertions)]
    fn details(&self) -> (&str, Location) { ("recursive", self.location) }

    #[cfg(debug_assertions)]
    fn fp(&self) -> Range<Option<usize>> { None..None }

    go_extra!();
}

impl<'a, I, E, S, O> Parser<'a, I, E, S> for Recursive<Direct<'a, I, O, E, S>>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
{
    type Output = O;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E> {
        M::invoke(&*self.parser(), inp)
    }

    #[cfg(debug_assertions)]
    fn details(&self) -> (&str, Location) { ("recursive", self.location) }

    #[cfg(debug_assertions)]
    fn fp(&self) -> Range<Option<usize>> { None..None }

    go_extra!();
}

#[track_caller]
pub fn recursive<
    'a,
    I: Input + ?Sized,
    E: Error<I>,
    S,
    A: Parser<'a, I, E, S> + 'a,
    F: FnOnce(Recursive<Direct<'a, I, A::Output, E, S>>) -> A,
>(
    f: F,
) -> Recursive<Direct<'a, I, A::Output, E, S>> {
    #[cfg(debug_assertions)]
    let location = *Location::caller();

    let rc = Rc::new_cyclic(|rc| {
        let rc: Weak<dyn Parser<'a, I, E, S, Output = A::Output>> = rc.clone() as _;
        let parser = Recursive {
            inner: RecursiveInner::Unowned(rc.clone()),
            #[cfg(debug_assertions)] location,
        };

        f(parser)
    });

    Recursive {
        inner: RecursiveInner::Owned(rc),
        #[cfg(debug_assertions)] location,
    }
}
