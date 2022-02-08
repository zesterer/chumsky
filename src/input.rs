#![allow(missing_docs)]

use core::{
    borrow::Borrow,
    ops::{Range, RangeFrom},
    marker::PhantomData,
    lazy::OnceCell,
};
use crate::Rc;

pub trait Input {
    type Offset: Copy;
    type Token;
    type Slice: ?Sized;

    fn start(&self) -> Self::Offset;

    fn next(&self, offset: Self::Offset) -> (Self::Offset, Option<Self::Token>);

    fn slice(&self, range: Range<Self::Offset>) -> &Self::Slice;
    unsafe fn slice_unchecked(&self, range: Range<Self::Offset>) -> &Self::Slice { self.slice(range) }
}

pub trait FullInput: Input {
    fn slice_from(&self, from: RangeFrom<Self::Offset>) -> &Self::Slice;
    unsafe fn slice_from_unchecked(&self, from: RangeFrom<Self::Offset>) -> &Self::Slice { self.slice_from(from) }
}

impl Input for str {
    type Offset = usize;
    type Token = char;
    type Slice = str;

    fn start(&self) -> Self::Offset { 0 }

    fn next(&self, offset: Self::Offset) -> (Self::Offset, Option<Self::Token>) {
        if offset < self.len() {
            let c = self[offset..].chars().next().unwrap();
            (offset + c.len_utf8(), Some(c))
        } else {
            (offset, None)
        }
    }

    fn slice(&self, range: Range<Self::Offset>) -> &Self::Slice { &self[range] }
    unsafe fn slice_unchecked(&self, range: Range<Self::Offset>) -> &Self::Slice { self.get_unchecked(range) }
}

impl FullInput for str {
    fn slice_from(&self, from: RangeFrom<Self::Offset>) -> &Self::Slice { &self[from] }
    unsafe fn slice_from_unchecked(&self, from: RangeFrom<Self::Offset>) -> &Self::Slice { self.get_unchecked(from) }
}

impl<T: Clone> Input for [T] {
    type Offset = usize;
    type Token = T;
    type Slice = [T];

    fn start(&self) -> Self::Offset { 0 }

    fn next(&self, offset: Self::Offset) -> (Self::Offset, Option<Self::Token>) {
        if let Some(tok) = self.get(offset) {
            (offset + 1, Some(tok.clone()))
        } else {
            (offset, None)
        }
    }

    fn slice(&self, range: Range<Self::Offset>) -> &Self::Slice { &self[range] }
    unsafe fn slice_unchecked(&self, range: Range<Self::Offset>) -> &Self::Slice { self.get_unchecked(range) }
}

impl<T: Clone> FullInput for [T] {
    fn slice_from(&self, from: RangeFrom<Self::Offset>) -> &Self::Slice { &self[from] }
    unsafe fn slice_from_unchecked(&self, from: RangeFrom<Self::Offset>) -> &Self::Slice { self.get_unchecked(from) }
}

pub struct InputRef<'a, I: Input + ?Sized> {
    input: &'a I,
    offset: I::Offset,
}

impl<'a, I: Input + ?Sized> Clone for InputRef<'a, I> {
    fn clone(&self) -> Self {
        Self {
            input: self.input,
            offset: self.offset,
        }
    }
}

impl<'a, I: Input + ?Sized> InputRef<'a, I> {
    fn new(input: &'a I) -> Self {
        Self {
            input,
            offset: input.start(),
        }
    }

    pub fn save(&mut self) -> I::Offset { self.offset }
    pub fn rewind(&mut self, offset: I::Offset) { self.offset = offset; }

    pub fn skip_while<F: FnMut(&I::Token) -> bool>(&mut self, mut f: F) {
        loop {
            let before = self.save();
            match self.next() {
                (_, Some(c)) if f(&c) => {},
                (_, Some(_) | None) => {
                    self.rewind(before);
                    break;
                },
            }
        }
    }

    pub fn next(&mut self) -> (I::Offset, Option<I::Token>) {
        let (offset, token) = self.input.next(self.offset);
        self.offset = offset;
        (offset, token)
    }

    pub fn slice(&self, range: Range<I::Offset>) -> &'a I::Slice { self.input.slice(range) }
    pub unsafe fn slice_unchecked(&self, range: Range<I::Offset>) -> &'a I::Slice { self.input.slice_unchecked(range) }

    pub fn slice_from(&self, from: RangeFrom<I::Offset>) -> &'a I::Slice where I: FullInput {
        self.input.slice_from(from)
    }
    pub unsafe fn slice_from_unchecked(&self, from: RangeFrom<I::Offset>) -> &'a I::Slice where I: FullInput {
        self.input.slice_from_unchecked(from)
    }
}

struct Stream<Buf> {
    buf: Buf,
}

pub trait Mode {
    type Output<T>;
    fn bind<T, F: FnOnce() -> T>(f: F) -> Self::Output<T>;
    fn map<T, U, F: FnOnce(T) -> U>(x: Self::Output<T>, f: F) -> Self::Output<U>;
    fn combine<T, U, V, F: FnOnce(T, U) -> V>(x: Self::Output<T>, y: Self::Output<U>, f: F) -> Self::Output<V>;
    fn vec<T>(x: Vec<Self::Output<T>>) -> Self::Output<Vec<T>>;
    fn array<T, const N: usize>(x: [Self::Output<T>; N]) -> Self::Output<[T; N]>;
    fn container<T, C: Container<T>>(x: C::Containing<Self::Output<T>>) -> Self::Output<C> where C: Container<T, Containing<T> = C>;

    fn invoke<'a, I: Input + ?Sized, P: Parser<'a, I> + ?Sized>(parser: &P, inp: &mut InputRef<'a, I>) -> Result<Self::Output<P::Output>, ()>;
}

pub struct Emit;
impl Mode for Emit {
    type Output<T> = T;
    fn bind<T, F: FnOnce() -> T>(f: F) -> Self::Output<T> { f() }
    fn map<T, U, F: FnOnce(T) -> U>(x: Self::Output<T>, f: F) -> Self::Output<U> { f(x) }
    fn combine<T, U, V, F: FnOnce(T, U) -> V>(x: Self::Output<T>, y: Self::Output<U>, f: F) -> Self::Output<V> { f(x, y) }
    fn vec<T>(x: Vec<Self::Output<T>>) -> Self::Output<Vec<T>> { x }
    fn array<T, const N: usize>(x: [Self::Output<T>; N]) -> Self::Output<[T; N]> { x }
    fn container<T, C: Container<T>>(x: C::Containing<Self::Output<T>>) -> Self::Output<C> where C: Container<T, Containing<T> = C> { x }

    fn invoke<'a, I: Input + ?Sized, P: Parser<'a, I> + ?Sized>(parser: &P, inp: &mut InputRef<'a, I>) -> Result<Self::Output<P::Output>, ()> {
        parser.go_emit(inp)
    }
}

pub struct Ignore;
impl Mode for Ignore {
    type Output<T> = ();
    fn bind<T, F: FnOnce() -> T>(_: F) -> Self::Output<T> {}
    fn map<T, U, F: FnOnce(T) -> U>(x: Self::Output<T>, f: F) -> Self::Output<U> {}
    fn combine<T, U, V, F: FnOnce(T, U) -> V>(x: Self::Output<T>, y: Self::Output<U>, f: F) -> Self::Output<V> {}
    fn vec<T>(x: Vec<Self::Output<T>>) -> Self::Output<Vec<T>> {}
    fn array<T, const N: usize>(x: [Self::Output<T>; N]) -> Self::Output<[T; N]> {}
    fn container<T, C: Container<T>>(x: C::Containing<Self::Output<T>>) -> Self::Output<C> where C: Container<T, Containing<T> = C> {}

    fn invoke<'a, I: Input + ?Sized, P: Parser<'a, I> + ?Sized>(parser: &P, inp: &mut InputRef<'a, I>) -> Result<Self::Output<P::Output>, ()> {
        parser.go_ignore(inp)
    }
}

macro_rules! go_extra {
    () => {
        fn go_emit(&self, inp: &mut InputRef<'a, I>) -> Result<<Emit as Mode>::Output<Self::Output>, ()> {
            self.go::<Emit>(inp)
        }
        fn go_ignore(&self, inp: &mut InputRef<'a, I>) -> Result<<Ignore as Mode>::Output<Self::Output>, ()> {
            self.go::<Ignore>(inp)
        }
    };
}

pub trait Parser<'a, I: Input + ?Sized> {
    type Output;

    fn parse(&self, input: &'a I) -> Result<Self::Output, ()> where Self: Sized {
        self.go::<Emit>(&mut InputRef::new(input))
    }

    #[doc(hidden)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, I>) -> Result<M::Output<Self::Output>, ()> where Self: Sized;

    #[doc(hidden)]
    fn go_emit(&self, inp: &mut InputRef<'a, I>) -> Result<<Emit as Mode>::Output<Self::Output>, ()>;
    #[doc(hidden)]
    fn go_ignore(&self, inp: &mut InputRef<'a, I>) -> Result<<Ignore as Mode>::Output<Self::Output>, ()>;

    fn map_slice<O, F: Fn(&'a I::Slice) -> O>(self, f: F) -> MapSlice<Self, F>
    where
        Self: Sized,
        I::Slice: 'a,
    {
        MapSlice { parser: self, mapper: f }
    }

    fn map<O, F: Fn(Self::Output) -> O>(self, f: F) -> Map<Self, F>
    where
        Self: Sized,
    {
        Map { parser: self, mapper: f }
    }

    fn ignored(self) -> Map<Self, fn(Self::Output) -> ()>
    where
        Self: Sized,
    {
        Map { parser: self, mapper: |_| {} }
    }

    fn to<O: Clone>(self, to: O) -> To<Self, O>
    where
        Self: Sized,
    {
        To { parser: self, to }
    }

    fn then<B: Parser<'a, I>>(self, other: B) -> Then<Self, B>
    where
        Self: Sized,
    {
        Then { parser_a: self, parser_b: other }
    }

    fn delimited_by<B: Parser<'a, I>, C: Parser<'a, I>>(self, start: B, end: C) -> DelimitedBy<Self, B, C>
    where
        Self: Sized,
    {
        DelimitedBy { parser: self, start, end }
    }

    fn or<B: Parser<'a, I, Output = Self::Output>>(self, other: B) -> Or<Self, B>
    where
        Self: Sized,
    {
        Or { parser_a: self, parser_b: other }
    }

    fn or_not(self) -> OrNot<Self>
    where
        Self: Sized,
    {
        OrNot { parser: self }
    }

    fn repeated(self) -> Repeated<Self, I, ()>
    where
        Self: Sized,
    {
        Repeated { parser: self, at_least: 0, phantom: PhantomData }
    }

    fn repeated_exactly<const N: usize>(self) -> RepeatedExactly<Self, N>
    where
        Self: Sized,
    {
        RepeatedExactly { parser: self }
    }

    fn padded(self) -> Padded<Self>
    where
        Self: Sized,
        I: Input,
        I::Token: Char,
    {
        Padded { parser: self }
    }
}

#[derive(Copy, Clone)]
pub struct End<I: ?Sized>(PhantomData<I>);

pub fn end<I: Input + ?Sized>() -> End<I> {
    End(PhantomData)
}

impl<'a, I> Parser<'a, I> for End<I>
where
    I: Input + ?Sized,
{
    type Output = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, I>) -> Result<M::Output<Self::Output>, ()> {
        match inp.next() {
            (_, None) => Ok(M::bind(|| ())),
            (_, Some(_)) => Err(()),
        }
    }

    go_extra!();
}

pub trait Seq<T> {
    type Iter<'a>: Iterator<Item = T>;
    fn iter(&self) -> Self::Iter<'_>;
}

impl<T: Clone> Seq<T> for T {
    type Iter<'a> = core::iter::Once<T>;
    fn iter(&self) -> Self::Iter<'_> { core::iter::once(self.clone()) }
}

impl<T: Clone, const N: usize> Seq<T> for [T; N] {
    type Iter<'a> = core::array::IntoIter<T, N>;
    fn iter(&self) -> Self::Iter<'_> { core::array::IntoIter::new(self.clone()) }
}

impl<'b, T: Clone, const N: usize> Seq<T> for &'b [T; N] {
    type Iter<'a> = core::array::IntoIter<T, N>;
    fn iter(&self) -> Self::Iter<'_> { core::array::IntoIter::new((*self).clone()) }
}

impl Seq<char> for str {
    type Iter<'a> = core::str::Chars<'a>;
    fn iter(&self) -> Self::Iter<'_> { self.chars() }
}

// impl<'b, T, C: Container<T>> Container<T> for &'b C {
//     type Iter<'a> = C::Iter<'a>;
//     fn iter(&self) -> Self::Iter<'_> { (*self).iter() }
// }

pub struct Just<S, I: ?Sized> {
    seq: S,
    phantom: PhantomData<I>,
}

impl<S: Copy, I: ?Sized> Copy for Just<S, I> {}
impl<S: Clone, I: ?Sized> Clone for Just<S, I> {
    fn clone(&self) -> Self {
        Self {
            seq: self.seq.clone(),
            phantom: PhantomData,
        }
    }
}

pub fn just<S, I>(seq: S) -> Just<S, I>
where
    I: Input + ?Sized,
    I::Token: PartialEq,
    S: Seq<I::Token>,
{
    Just {
        seq,
        phantom: PhantomData,
    }
}

impl<'a, I, S> Parser<'a, I> for Just<S, I>
where
    I: Input + ?Sized,
    I::Token: PartialEq,
    S: Seq<I::Token>,
{
    type Output = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, I>) -> Result<M::Output<Self::Output>, ()> {
        let mut items = self.seq.iter();
        loop {
            match items.next() {
                Some(next) => match inp.next() {
                    (_, Some(tok)) if next == tok => {},
                    (_, Some(_) | None) => break Err(()),
                },
                None => break Ok(M::bind(|| ())),
            }
        }
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct MapSlice<A, F> {
    parser: A,
    mapper: F,
}

impl<'a, I, A, F, O> Parser<'a, I> for MapSlice<A, F>
where
    I: Input + ?Sized,
    I::Slice: 'a,
    A: Parser<'a, I>,
    F: Fn(&'a I::Slice) -> O,
{
    type Output = O;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, I>) -> Result<M::Output<Self::Output>, ()> {
        let before = inp.save();
        match self.parser.go::<Ignore>(inp) {
            Ok(_) => {
                let after = inp.save();
                Ok(M::bind(|| (self.mapper)(inp.slice(before..after))))
            },
            Err(e) => Err(e),
        }
    }

    go_extra!();
}

pub struct Filter<F, I: ?Sized> {
    filter: F,
    phantom: PhantomData<I>,
}

impl<F: Copy, I: ?Sized> Copy for Filter<F, I> {}
impl<F: Clone, I: ?Sized> Clone for Filter<F, I> {
    fn clone(&self) -> Self {
        Self {
            filter: self.filter.clone(),
            phantom: PhantomData,
        }
    }
}

pub fn filter<F: Fn(&I::Token) -> bool, I: Input + ?Sized>(filter: F) -> Filter<F, I> {
    Filter { filter, phantom: PhantomData }
}

impl<'a, I, F> Parser<'a, I> for Filter<F, I>
where
    I: Input + ?Sized,
    F: Fn(&I::Token) -> bool,
{
    type Output = I::Token;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, I>) -> Result<M::Output<Self::Output>, ()> {
        match inp.next() {
            (_, Some(tok)) if (self.filter)(&tok) => Ok(M::bind(|| tok)),
            (_, Some(_) | None) => Err(()),
        }
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct Map<A, F> {
    parser: A,
    mapper: F,
}

impl<'a, I, A, F, O> Parser<'a, I> for Map<A, F>
where
    I: Input + ?Sized,
    A: Parser<'a, I>,
    F: Fn(A::Output) -> O,
{
    type Output = O;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, I>) -> Result<M::Output<Self::Output>, ()> {
        self.parser.go::<M>(inp)
            .map(|out| M::map(out, &self.mapper))
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct To<A, O> {
    parser: A,
    to: O,
}

impl<'a, I, A, O> Parser<'a, I> for To<A, O>
where
    I: Input + ?Sized,
    A: Parser<'a, I>,
    O: Clone,
{
    type Output = O;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, I>) -> Result<M::Output<Self::Output>, ()> {
        self.parser.go::<M>(inp)
            .map(|_| M::bind(|| self.to.clone()))
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct Then<A, B> {
    parser_a: A,
    parser_b: B,
}

impl<'a, I, A, B> Parser<'a, I> for Then<A, B>
where
    I: Input + ?Sized,
    A: Parser<'a, I>,
    B: Parser<'a, I>,
{
    type Output = (A::Output, B::Output);

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, I>) -> Result<M::Output<Self::Output>, ()> {
        let a = self.parser_a.go::<M>(inp)?;
        let b = self.parser_b.go::<M>(inp)?;
        Ok(M::combine(a, b, |a, b| (a, b)))
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct DelimitedBy<A, B, C> {
    parser: A,
    start: B,
    end: C,
}

impl<'a, I, A, B, C> Parser<'a, I> for DelimitedBy<A, B, C>
where
    I: Input + ?Sized,
    A: Parser<'a, I>,
    B: Parser<'a, I>,
    C: Parser<'a, I>,
{
    type Output = A::Output;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, I>) -> Result<M::Output<Self::Output>, ()> {
        let _ = self.start.go::<Ignore>(inp)?;
        let b = self.parser.go::<M>(inp)?;
        let _ = self.end.go::<Ignore>(inp)?;
        Ok(b)
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct Or<A, B> {
    parser_a: A,
    parser_b: B,
}

impl<'a, I, A, B> Parser<'a, I> for Or<A, B>
where
    I: Input + ?Sized,
    A: Parser<'a, I>,
    B: Parser<'a, I, Output = A::Output>,
{
    type Output = A::Output;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, I>) -> Result<M::Output<Self::Output>, ()> {
        let before = inp.save();
        match self.parser_a.go::<M>(inp) {
            Ok(out) => Ok(out),
            Err(()) => {
                inp.rewind(before);
                self.parser_b.go::<M>(inp)
            },
        }
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct Choice<T, O> {
    parsers: T,
    phantom: PhantomData<O>,
}

pub fn choice<T, O>(parsers: T) -> Choice<T, O> {
    Choice { parsers, phantom: PhantomData }
}

macro_rules! impl_for_tuple {
    () => {};
    ($head:ident $($X:ident)*) => {
        impl_for_tuple!($($X)*);
        impl_for_tuple!(~ $head $($X)*);
    };
    (~ $($X:ident)*) => {
        #[allow(unused_variables, non_snake_case)]
        impl<'a, I, $($X: Parser<'a, I, Output = O>),*, O> Parser<'a, I> for Choice<($($X,)*), O>
        where
            I: Input + ?Sized,
        {
            type Output = O;

            fn go<M: Mode>(&self, inp: &mut InputRef<'a, I>) -> Result<M::Output<Self::Output>, ()> {
                let before = inp.save();

                let Choice { parsers: ($($X,)*), .. } = self;

                $(
                    match $X.go::<M>(inp) {
                        Ok(out) => return Ok(out),
                        Err(()) => inp.rewind(before),
                    };
                )*

                Err(())
            }

            go_extra!();
        }
    };
}

impl_for_tuple!(A_ B_ C_ D_ E_ F_ G_ H_ I_ J_ K_ L_ M_ N_ O_ P_ Q_ S_ T_ U_ V_ W_ X_ Y_ Z_);

pub trait Char {
    fn is_whitespace(&self) -> bool;
}

impl Char for char {
    fn is_whitespace(&self) -> bool { (*self).is_whitespace() }
}

impl Char for u8 {
    fn is_whitespace(&self) -> bool { self.is_ascii_whitespace() }
}

#[derive(Clone)]
pub struct Padded<A> {
    parser: A,
}

impl<'a, I, A> Parser<'a, I> for Padded<A>
where
    I: Input + ?Sized,
    I::Token: Char,
    A: Parser<'a, I>,
{
    type Output = A::Output;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, I>) -> Result<M::Output<Self::Output>, ()> {
        inp.skip_while(|c| c.is_whitespace());
        let out = self.parser.go::<M>(inp)?;
        inp.skip_while(|c| c.is_whitespace());
        Ok(out)
    }

    go_extra!();
}

pub trait Container<T>: Default {
    type Containing<U>: Container<U>;
    fn push(&mut self, item: T);
}

impl<T> Container<T> for () {
    type Containing<U> = ();
    fn push(&mut self, _: T) {}
}

impl<T> Container<T> for Vec<T> {
    type Containing<U> = Vec<U>;
    fn push(&mut self, item: T) {
        (*self).push(item);
    }
}

pub struct Repeated<A, I: ?Sized, C = ()> {
    parser: A,
    at_least: usize,
    phantom: PhantomData<(C, I)>,
}

impl<A: Copy, I: ?Sized, C> Copy for Repeated<A, I, C> {}
impl<A: Copy, I: ?Sized, C> Clone for Repeated<A, I, C> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            at_least: self.at_least,
            phantom: PhantomData,
        }
    }
}

impl<'a, A: Parser<'a, I>, I: Input + ?Sized, C> Repeated<A, I, C> {
    pub fn at_least(self, at_least: usize) -> Self {
        Self { at_least, .. self }
    }

    pub fn collect<D: Container<A::Output>>(self) -> Repeated<A, I, D>
        where A: Parser<'a, I>
    {
        Repeated {
            parser: self.parser,
            at_least: self.at_least,
            phantom: PhantomData,
        }
    }
}

impl<'a, I, A, C> Parser<'a, I> for Repeated<A, I, C>
where
    I: Input + ?Sized,
    A: Parser<'a, I>,
    C: Container<A::Output>,
{
    type Output = C;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, I>) -> Result<M::Output<Self::Output>, ()> {
        let mut count = 0;
        let mut output = M::bind::<C, _>(|| C::default());
        loop {
            let before = inp.save();
            match self.parser.go::<M>(inp) {
                Ok(out) => {
                    output = M::map(output, |mut output| {
                        M::map(out, |out| output.push(out));
                        output
                    });
                    count += 1;
                },
                Err(()) => {
                    inp.rewind(before);
                    break if count >= self.at_least {
                        Ok(output)
                    } else {
                        Err(())
                    };
                },
            }
        }
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct OrNot<A> {
    parser: A,
}

impl<'a, I, A> Parser<'a, I> for OrNot<A>
where
    I: Input + ?Sized,
    A: Parser<'a, I>,
{
    type Output = Option<A::Output>;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, I>) -> Result<M::Output<Self::Output>, ()> {
        let before = inp.save();
        Ok(match self.parser.go::<M>(inp) {
            Ok(o) => M::map(o, Some),
            Err(()) => {
                inp.rewind(before);
                M::bind(|| None)
            },
        })
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct RepeatedExactly<A, const N: usize> {
    parser: A,
}

impl<'a, I, A, const N: usize> Parser<'a, I> for RepeatedExactly<A, N>
where
    I: Input + ?Sized,
    A: Parser<'a, I>,
{
    type Output = [A::Output; N];

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, I>) -> Result<M::Output<Self::Output>, ()> {
        use std::mem::MaybeUninit;

        let mut i = 0;
        let mut output = MaybeUninit::uninit_array();
        loop {
            let before = inp.save();
            match self.parser.go::<M>(inp) {
                Ok(out) => {
                    output[i].write(out);
                    i += 1;
                    if i == N {
                        // SAFETY: All entries with an index < i are filled
                        break Ok(M::array(unsafe { MaybeUninit::array_assume_init(output) }));
                    }
                },
                Err(()) => {
                    inp.rewind(before);
                    // SAFETY: All entries with an index < i are filled
                    output[..i]
                        .iter_mut()
                        .for_each(|o| unsafe { o.assume_init_drop() });
                    break Err(());
                },
            }
        }
    }

    go_extra!();
}

pub struct RecursiveInner<'a, I: ?Sized, O> {
    this: Rc<OnceCell<Self>>,
    parser: Box<dyn Parser<'a, I, Output = O> + 'a>,
}

pub struct Recursive<'a, I: ?Sized, O> {
    inner: Rc<OnceCell<RecursiveInner<'a, I, O>>>,
}

impl<'a, I: ?Sized, O> Clone for Recursive<'a, I, O> {
    fn clone(&self) -> Self {
        Self { inner: self.inner.clone() }
    }
}

pub fn recursive<'a, I: Input + ?Sized, A: Parser<'a, I> + 'a, F: FnOnce(Recursive<'a, I, A::Output>) -> A>(f: F) -> Recursive<'a, I, A::Output> {
    let recursive = Recursive { inner: Rc::new(OnceCell::new()) };
    recursive.inner
        .set(RecursiveInner {
            this: recursive.inner.clone(),
            parser: Box::new(f(recursive.clone())),
        })
        .ok()
        .expect("recursive parser already declared");
    recursive
}

impl<'a, I, O> Parser<'a, I> for Recursive<'a, I, O>
where
    I: Input + ?Sized,
{
    type Output = O;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, I>) -> Result<M::Output<Self::Output>, ()> {
        M::invoke(&*self.inner
            .get()
            .expect("recursive parser used before definition")
            .parser, inp)
    }

    go_extra!();
}

#[test]
fn zero_copy() {
    #[derive(PartialEq, Debug)]
    enum Token<'a> {
        Ident(&'a str),
        String(&'a str),
    }

    #[derive(Clone)]
    enum TokenTest {
        Root,
        Branch(Box<Self>),
    }

    fn parser2() -> impl Parser<'static, str, Output = TokenTest> {
        recursive(|token| {
            token
                .delimited_by(just('c'), just('c'))
                .map(Box::new)
                .map(TokenTest::Branch)
                .or(just('!').to(TokenTest::Root))
        })
    }

    fn parser<'a>() -> impl Parser<'a, str, Output = [Token<'a>; 6]> {
        let ident = filter(|c: &char| c.is_alphanumeric())
            .repeated()
            .at_least(1)
            .map_slice(Token::Ident);

        let string = just('"')
            .then(filter(|c: &char| *c != '"').repeated())
            .then(just('"'))
            .map_slice(Token::String);

        ident
            .or(string)
            .padded()
            .repeated_exactly()
    }

    assert_eq!(
        parser().parse(r#"hello "world" these are "test" tokens"#),
        Ok([
            Token::Ident("hello"),
            Token::String("\"world\""),
            Token::Ident("these"),
            Token::Ident("are"),
            Token::String("\"test\""),
            Token::Ident("tokens"),
        ]),
    );
}

#[test]
fn unicode_str() {
    let s = "🄯🄚🹠🴎🄐🝋🰏🄂🬯🈦g🸵🍩🕔🈳2🬙🨞🅢🭳🎅h🵚🧿🏩🰬k🠡🀔🈆🝹🤟🉗🴟📵🰄🤿🝜🙘🹄5🠻🡉🱖🠓";
    let mut s = InputRef::new(s);

    while let (_, Some(c)) = s.next() {
        std::hint::black_box(c);
    }
}
