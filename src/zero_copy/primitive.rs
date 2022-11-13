use super::*;

pub struct End<I: ?Sized>(PhantomData<I>);

pub const fn end<I: Input + ?Sized>() -> End<I> {
    End(PhantomData)
}

impl<I: ?Sized> Copy for End<I> {}
impl<I: ?Sized> Clone for End<I> {
    fn clone(&self) -> Self {
        End(PhantomData)
    }
}

impl<'a, I, E, S> Parser<'a, I, (), E, S> for End<I>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, (), E> {
        let before = inp.save();
        match inp.next() {
            (_, None) => Ok(M::bind(|| ())),
            (at, Some(tok)) => Err(Located::at(
                at,
                E::expected_found(None, Some(tok), inp.span_since(before)),
            )),
        }
    }

    go_extra!(());
}

pub struct Empty<I: ?Sized>(PhantomData<I>);

pub const fn empty<I: Input + ?Sized>() -> Empty<I> {
    Empty(PhantomData)
}

impl<I: ?Sized> Copy for Empty<I> {}
impl<I: ?Sized> Clone for Empty<I> {
    fn clone(&self) -> Self {
        Empty(PhantomData)
    }
}

impl<'a, I, E, S> Parser<'a, I, (), E, S> for Empty<I>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
{
    fn go<M: Mode>(&self, _: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, (), E> {
        Ok(M::bind(|| ()))
    }

    go_extra!(());
}

pub trait Seq<T> {
    type Iter<'a>: Iterator<Item = T>
    where
        Self: 'a;
    fn iter(&self) -> Self::Iter<'_>;
}

impl<T: Clone> Seq<T> for T {
    type Iter<'a> = core::iter::Once<T>
    where
        Self: 'a;
    fn iter(&self) -> Self::Iter<'_> {
        core::iter::once(self.clone())
    }
}

impl<T: Clone, const N: usize> Seq<T> for [T; N] {
    type Iter<'a> = core::array::IntoIter<T, N>
    where
        Self: 'a;
    fn iter(&self) -> Self::Iter<'_> {
        core::array::IntoIter::new(self.clone())
    }
}

impl<'b, T: Clone, const N: usize> Seq<T> for &'b [T; N] {
    type Iter<'a> = core::array::IntoIter<T, N>
    where
        Self: 'a;
    fn iter(&self) -> Self::Iter<'_> {
        core::array::IntoIter::new((*self).clone())
    }
}

impl Seq<char> for str {
    type Iter<'a> = core::str::Chars<'a>
    where
        Self: 'a;
    fn iter(&self) -> Self::Iter<'_> {
        self.chars()
    }
}

impl<'b> Seq<char> for &'b str {
    type Iter<'a> = core::str::Chars<'a>
    where
        Self: 'a;
    fn iter(&self) -> Self::Iter<'_> {
        self.chars()
    }
}

impl Seq<char> for String {
    type Iter<'a> = core::str::Chars<'a>
    where
        Self: 'a;
    fn iter(&self) -> Self::Iter<'_> {
        self.chars()
    }
}

// impl<'b, T, C: Container<T>> Container<T> for &'b C {
//     type Iter<'a> = C::Iter<'a>;
//     fn iter(&self) -> Self::Iter<'_> { (*self).iter() }
// }

pub struct Just<T, I: ?Sized, E = (), S = ()> {
    seq: T,
    phantom: PhantomData<(E, S, I)>,
}

impl<T: Copy, I: ?Sized, E, S> Copy for Just<T, I, E, S> {}
impl<T: Clone, I: ?Sized, E, S> Clone for Just<T, I, E, S> {
    fn clone(&self) -> Self {
        Self {
            seq: self.seq.clone(),
            phantom: PhantomData,
        }
    }
}

pub const fn just<T, I, E, S>(seq: T) -> Just<T, I, E, S>
where
    I: Input + ?Sized,
    E: Error<I>,
    I::Token: PartialEq,
    T: Seq<I::Token> + Clone,
{
    Just {
        seq,
        phantom: PhantomData,
    }
}

impl<'a, I, E, S, T> Parser<'a, I, T, E, S> for Just<T, I, E, S>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    I::Token: PartialEq,
    T: Seq<I::Token> + Clone,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, T, E> {
        let mut items = self.seq.iter();
        loop {
            match items.next() {
                Some(next) => {
                    let before = inp.save();
                    match inp.next() {
                        (_, Some(tok)) if next == tok => {}
                        (at, tok) => {
                            break Err(Located::at(
                                at,
                                E::expected_found(Some(Some(next)), tok, inp.span_since(before)),
                            ))
                        }
                    }
                }
                None => break Ok(M::bind(|| self.seq.clone())),
            }
        }
    }

    go_extra!(T);
}

pub struct OneOf<T, I: ?Sized, E = (), S = ()> {
    seq: T,
    phantom: PhantomData<(E, S, I)>,
}

impl<T: Copy, I: ?Sized, E, S> Copy for OneOf<T, I, E, S> {}
impl<T: Clone, I: ?Sized, E, S> Clone for OneOf<T, I, E, S> {
    fn clone(&self) -> Self {
        Self {
            seq: self.seq.clone(),
            phantom: PhantomData,
        }
    }
}

pub const fn one_of<T, I, E, S>(seq: T) -> OneOf<T, I, E, S>
where
    I: Input + ?Sized,
    E: Error<I>,
    I::Token: PartialEq,
    T: Seq<I::Token> + Clone,
{
    OneOf {
        seq,
        phantom: PhantomData,
    }
}

impl<'a, I, E, S, T> Parser<'a, I, I::Token, E, S> for OneOf<T, I, E, S>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    I::Token: PartialEq,
    T: Seq<I::Token> + Clone,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, I::Token, E> {
        let before = inp.save();
        match inp.next() {
            (_, Some(tok)) if self.seq.iter().any(|not| not == tok) => Ok(M::bind(|| tok)),
            (at, found) => Err(Located::at(
                at,
                E::expected_found(self.seq.iter().map(Some), found, inp.span_since(before)),
            )),
        }
    }

    go_extra!(I::Token);
}

pub struct NoneOf<T, I: ?Sized, E = (), S = ()> {
    seq: T,
    phantom: PhantomData<(E, S, I)>,
}

impl<T: Copy, I: ?Sized, E, S> Copy for NoneOf<T, I, E, S> {}
impl<T: Clone, I: ?Sized, E, S> Clone for NoneOf<T, I, E, S> {
    fn clone(&self) -> Self {
        Self {
            seq: self.seq.clone(),
            phantom: PhantomData,
        }
    }
}

pub const fn none_of<T, I, E, S>(seq: T) -> NoneOf<T, I, E, S>
where
    I: Input + ?Sized,
    E: Error<I>,
    I::Token: PartialEq,
    T: Seq<I::Token> + Clone,
{
    NoneOf {
        seq,
        phantom: PhantomData,
    }
}

impl<'a, I, E, S, T> Parser<'a, I, I::Token, E, S> for NoneOf<T, I, E, S>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    I::Token: PartialEq,
    T: Seq<I::Token> + Clone,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, I::Token, E> {
        let before = inp.save();
        match inp.next() {
            (_, Some(tok)) if self.seq.iter().all(|not| not != tok) => Ok(M::bind(|| tok)),
            (at, found) => Err(Located::at(
                at,
                E::expected_found(None, found, inp.span_since(before)),
            )),
        }
    }

    go_extra!(I::Token);
}

pub struct Any<I: ?Sized, E, S = ()> {
    phantom: PhantomData<(E, S, I)>,
}

impl<I: ?Sized, E, S> Copy for Any<I, E, S> {}
impl<I: ?Sized, E, S> Clone for Any<I, E, S> {
    fn clone(&self) -> Self {
        Self {
            phantom: PhantomData,
        }
    }
}

impl<'a, I, E, S> Parser<'a, I, I::Token, E, S> for Any<I, E, S>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, I::Token, E> {
        let before = inp.save();
        match inp.next() {
            (_, Some(tok)) => Ok(M::bind(|| tok)),
            (at, found) => Err(Located::at(
                at,
                E::expected_found(None, found, inp.span_since(before)),
            )),
        }
    }

    go_extra!(I::Token);
}

pub const fn any<I: Input + ?Sized, E: Error<I>, S>() -> Any<I, E, S> {
    Any {
        phantom: PhantomData,
    }
}

pub struct TakeUntil<P, I: ?Sized, OP, C = (), E = (), S = ()> {
    until: P,
    // FIXME try remove OP? See comment in Map declaration
    phantom: PhantomData<(OP, C, E, S, I)>,
}

impl<'a, I, E, S, P, OP, C> TakeUntil<P, OP, I, C, E, S>
where
    I: Input,
    E: Error<I>,
    S: 'a,
    P: Parser<'a, I, OP, E, S>,
{
    pub fn collect<D: Container<OP>>(self) -> TakeUntil<P, OP, D> {
        TakeUntil {
            until: self.until,
            phantom: PhantomData,
        }
    }
}

impl<P: Copy, I: ?Sized, C, E, S> Copy for TakeUntil<P, I, C, E, S> {}
impl<P: Clone, I: ?Sized, C, E, S> Clone for TakeUntil<P, I, C, E, S> {
    fn clone(&self) -> Self {
        TakeUntil {
            until: self.until.clone(),
            phantom: PhantomData,
        }
    }
}

pub const fn take_until<'a, P, OP, I, E, S>(until: P) -> TakeUntil<P, I, (), E, S>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    P: Parser<'a, I, OP, E, S>,
{
    TakeUntil {
        until,
        phantom: PhantomData,
    }
}

impl<'a, P, OP, I, E, S, C> Parser<'a, I, (C, OP), E, S> for TakeUntil<P, I, C, E, S>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    P: Parser<'a, I, OP, E, S>,
    C: Container<I::Token>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, (C, OP), E> {
        let mut output = M::bind(|| C::default());

        loop {
            let start = inp.save();
            let e = match self.until.go::<M>(inp) {
                Ok(out) => break Ok(M::combine(output, out, |output, out| (output, out))),
                Err(e) => e,
            };

            inp.rewind(start);

            match inp.next() {
                (_, Some(tok)) => {
                    output = M::map(output, |mut output: C| {
                        output.push(tok);
                        output
                    })
                }
                (_, None) => break Err(e),
            }
        }
    }

    go_extra!((C, OP));
}

pub struct Todo<I: ?Sized, E>(PhantomData<(E, I)>);

impl<I: ?Sized, E> Copy for Todo<I, E> {}
impl<I: ?Sized, E> Clone for Todo<I, E> {
    fn clone(&self) -> Self {
        *self
    }
}

pub const fn todo<I: Input + ?Sized, E: Error<I>>() -> Todo<I, E> {
    Todo(PhantomData)
}

impl<'a, I, E, S> Parser<'a, I, (), E, S> for Todo<I, E>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
{
    fn go<M: Mode>(&self, _inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, (), E> {
        todo!("Attempted to use an unimplemented parser")
    }

    go_extra!(());
}

pub struct Choice<T, O> {
    parsers: T,
    phantom: PhantomData<O>,
}

impl<T: Copy, O> Copy for Choice<T, O> {}
impl<T: Clone, O> Clone for Choice<T, O> {
    fn clone(&self) -> Self {
        Self {
            parsers: self.parsers.clone(),
            phantom: PhantomData,
        }
    }
}

pub const fn choice<T, O>(parsers: T) -> Choice<T, O> {
    Choice {
        parsers,
        phantom: PhantomData,
    }
}

macro_rules! impl_choice_for_tuple {
    () => {};
    ($head:ident $($X:ident)*) => {
        impl_choice_for_tuple!($($X)*);
        impl_choice_for_tuple!(~ $head $($X)*);
    };
    (~ $($X:ident)*) => {
        #[allow(unused_variables, non_snake_case)]
        impl<'a, I, E, S, $($X),*, O> Parser<'a, I, O, E, S> for Choice<($($X,)*), O>
        where
            I: Input + ?Sized,
            E: Error<I>,
            S: 'a,
            $($X: Parser<'a, I, O, E, S>),*
        {
            fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, O, E> {
                let before = inp.save();

                let Choice { parsers: ($($X,)*), .. } = self;

                let mut err: Option<Located<E>> = None;
                $(
                    match $X.go::<M>(inp) {
                        Ok(out) => return Ok(out),
                        Err(e) => {
                            // TODO: prioritise errors
                            err = Some(match err {
                                Some(err) => err.prioritize(e, |a, b| a.merge(b)),
                                None => e,
                            });
                            inp.rewind(before);
                        },
                    };
                )*

                Err(err.unwrap_or_else(|| Located::at(inp.last_pos(), E::expected_found(None, None, inp.span_since(before)))))
            }

            go_extra!(O);
        }
    };
}

impl_choice_for_tuple!(A_ B_ C_ D_ E_ F_ G_ H_ I_ J_ K_ L_ M_ N_ O_ P_ Q_ S_ T_ U_ V_ W_ X_ Y_ Z_);

#[derive(Copy, Clone)]
pub struct Group<T> {
    parsers: T,
}

pub const fn group<T>(parsers: T) -> Group<T> {
    Group { parsers }
}

macro_rules! flatten_map {
    // map a single element into a 1-tuple
    (<$M:ident> $head:ident) => {
        $M::map(
            $head,
            |$head| ($head,),
        )
    };
    // combine two elements into a 2-tuple
    (<$M:ident> $head1:ident $head2:ident) => {
        $M::combine(
            $head1,
            $head2,
            |$head1, $head2| ($head1, $head2),
        )
    };
    // combine and flatten n-tuples from recursion
    (<$M:ident> $head:ident $($X:ident)+) => {
        $M::combine(
            $head,
            flatten_map!(
                <$M>
                $($X)+
            ),
            |$head, ($($X),+)| ($head, $($X),+),
        )
    };
}

macro_rules! impl_group_for_tuple {
    () => {};
    ($head:ident $($X:ident)*) => {
        impl_group_for_tuple!($($X)*);
        impl_group_for_tuple!(~ $head $($X)*);
    };
    (~ $($X:ident)*) => {
        #[allow(unused_variables, non_snake_case)]
        impl<'a, I, E, S, $($X,)* $(O$X),*> Parser<'a, I, ($(O$X),*), E, S> for Group<($($X,)*)>
        where
            I: Input + ?Sized,
            E: Error<I>,
            S: 'a,
            $($X: Parser<'a, I, O$X, E, S>),*
        {
            fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, ($(O$X),*), E> {
                let Group { parsers: ($($X,)*) } = self;

                $(
                    let $X = $X.go::<M>(inp)?;
                )*

                Ok(flatten_map!(<M> $($X)*))
            }

            go_extra!(($(O$X),*));
        }
    };
}

// FIXME: uncomment and fix trait bounds!! I(bew) don't know how to write advanced macros like this
//impl_group_for_tuple!(A_ B_ C_ D_ E_ F_ G_ H_ I_ J_ K_ L_ M_ N_ O_ P_ Q_ S_ T_ U_ V_ W_ X_ Y_ Z_);
