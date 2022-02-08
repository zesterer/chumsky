#![allow(missing_docs)]

use core::{
    cmp::Eq,
    hash::Hash,
    ops::{Range, RangeFrom},
    marker::PhantomData,
    lazy::OnceCell,
};
use crate::Rc;
use std::collections::HashMap;

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
            // TODO: Can we `unwrap_unchecked` here?
            let c = unsafe { self.get_unchecked(offset..).chars().next().unwrap() };
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

pub struct InputRef<'a, 'parse, I: Input + ?Sized, S> {
    input: &'a I,
    offset: I::Offset,
    state: &'parse mut S,
}

impl<'a, 'parse, I: Input + ?Sized, S> InputRef<'a, 'parse, I, S> {
    fn new(input: &'a I, state: &'parse mut S) -> Self {
        Self {
            input,
            offset: input.start(),
            state,
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
    fn array<T, const N: usize>(x: [Self::Output<T>; N]) -> Self::Output<[T; N]>;

    fn invoke<'a, I: Input + ?Sized, S, P: Parser<'a, I, S> + ?Sized>(parser: &P, inp: &mut InputRef<'a, '_, I, S>) -> Result<Self::Output<P::Output>, ()>;
}

pub struct Emit;
impl Mode for Emit {
    type Output<T> = T;
    fn bind<T, F: FnOnce() -> T>(f: F) -> Self::Output<T> { f() }
    fn map<T, U, F: FnOnce(T) -> U>(x: Self::Output<T>, f: F) -> Self::Output<U> { f(x) }
    fn combine<T, U, V, F: FnOnce(T, U) -> V>(x: Self::Output<T>, y: Self::Output<U>, f: F) -> Self::Output<V> { f(x, y) }
    fn array<T, const N: usize>(x: [Self::Output<T>; N]) -> Self::Output<[T; N]> { x }

    fn invoke<'a, I: Input + ?Sized, S, P: Parser<'a, I, S> + ?Sized>(parser: &P, inp: &mut InputRef<'a, '_, I, S>) -> Result<Self::Output<P::Output>, ()> {
        parser.go_emit(inp)
    }
}

pub struct Check;
impl Mode for Check {
    type Output<T> = ();
    fn bind<T, F: FnOnce() -> T>(_: F) -> Self::Output<T> {}
    fn map<T, U, F: FnOnce(T) -> U>(x: Self::Output<T>, f: F) -> Self::Output<U> {}
    fn combine<T, U, V, F: FnOnce(T, U) -> V>(x: Self::Output<T>, y: Self::Output<U>, f: F) -> Self::Output<V> {}
    fn array<T, const N: usize>(x: [Self::Output<T>; N]) -> Self::Output<[T; N]> {}

    fn invoke<'a, I: Input + ?Sized, S, P: Parser<'a, I, S> + ?Sized>(parser: &P, inp: &mut InputRef<'a, '_, I, S>) -> Result<Self::Output<P::Output>, ()> {
        parser.go_check(inp)
    }
}

macro_rules! go_extra {
    () => {
        fn go_emit(&self, inp: &mut InputRef<'a, '_, I, S>) -> Result<<Emit as Mode>::Output<Self::Output>, ()> {
            self.go::<Emit>(inp)
        }
        fn go_check(&self, inp: &mut InputRef<'a, '_, I, S>) -> Result<<Check as Mode>::Output<Self::Output>, ()> {
            self.go::<Check>(inp)
        }
    };
}

pub trait Parser<'a, I: Input + ?Sized, S: 'a = ()> {
    type Output;

    fn parse(&self, input: &'a I) -> Result<Self::Output, ()>
    where
        Self: Sized,
        S: Default,
    {
        self.go::<Emit>(&mut InputRef::new(input, &mut S::default()))
    }

    fn parse_with_state(&self, input: &'a I, state: &mut S) -> Result<Self::Output, ()>
    where
        Self: Sized,
    {
        self.go::<Emit>(&mut InputRef::new(input, state))
    }

    fn check(&self, input: &'a I) -> Result<(), ()>
    where
        Self: Sized,
        S: Default,
    {
        self.go::<Check>(&mut InputRef::new(input, &mut S::default()))
    }

    #[doc(hidden)]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> Result<M::Output<Self::Output>, ()> where Self: Sized;

    #[doc(hidden)]
    fn go_emit(&self, inp: &mut InputRef<'a, '_, I, S>) -> Result<<Emit as Mode>::Output<Self::Output>, ()>;
    #[doc(hidden)]
    fn go_check(&self, inp: &mut InputRef<'a, '_, I, S>) -> Result<<Check as Mode>::Output<Self::Output>, ()>;

    fn map_slice<O, F: Fn(&'a I::Slice) -> O>(self, f: F) -> MapSlice<Self, F, S>
    where
        Self: Sized,
        I::Slice: 'a,
    {
        MapSlice { parser: self, mapper: f, phantom: PhantomData }
    }

    fn map<O, F: Fn(Self::Output) -> O>(self, f: F) -> Map<Self, F>
    where
        Self: Sized,
    {
        Map { parser: self, mapper: f }
    }

    fn ignored(self) -> Ignored<Self, S>
    where
        Self: Sized,
    {
        Ignored { parser: self, to: (), phantom: PhantomData }
    }

    fn to<O: Clone>(self, to: O) -> To<Self, O>
    where
        Self: Sized,
    {
        To { parser: self, to, phantom: PhantomData }
    }

    fn then<B: Parser<'a, I, S>>(self, other: B) -> Then<Self, B>
    where
        Self: Sized,
    {
        Then { parser_a: self, parser_b: other }
    }

    fn delimited_by<B: Parser<'a, I, S>, C: Parser<'a, I, S>>(self, start: B, end: C) -> DelimitedBy<Self, B, C>
    where
        Self: Sized,
    {
        DelimitedBy { parser: self, start, end }
    }

    fn or<B: Parser<'a, I, S, Output = Self::Output>>(self, other: B) -> Or<Self, B>
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

    fn repeated(self) -> Repeated<Self, I, (), S>
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

impl<'a, I, S> Parser<'a, I, S> for End<I>
where
    I: Input + ?Sized,
    S: 'a,
{
    type Output = ();

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> Result<M::Output<Self::Output>, ()> {
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

pub struct Just<T, I: ?Sized, S = ()> {
    seq: T,
    phantom: PhantomData<(S, I)>,
}

impl<T: Copy, I: ?Sized, S> Copy for Just<T, I, S> {}
impl<T: Clone, I: ?Sized, S> Clone for Just<T, I, S> {
    fn clone(&self) -> Self {
        Self {
            seq: self.seq.clone(),
            phantom: PhantomData,
        }
    }
}

pub fn just<T, I, S>(seq: T) -> Just<T, I, S>
where
    I: Input + ?Sized,
    I::Token: PartialEq,
    T: Seq<I::Token> + Clone,
{
    Just {
        seq,
        phantom: PhantomData,
    }
}

impl<'a, I, S, T> Parser<'a, I, S> for Just<T, I, S>
where
    I: Input + ?Sized,
    S: 'a,
    I::Token: PartialEq,
    T: Seq<I::Token> + Clone,
{
    type Output = T;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> Result<M::Output<Self::Output>, ()> {
        let mut items = self.seq.iter();
        loop {
            match items.next() {
                Some(next) => match inp.next() {
                    (_, Some(tok)) if next == tok => {},
                    (_, Some(_) | None) => break Err(()),
                },
                None => break Ok(M::bind(|| self.seq.clone())),
            }
        }
    }

    go_extra!();
}

pub struct MapSlice<A, F, S = ()> {
    parser: A,
    mapper: F,
    phantom: PhantomData<S>,
}

impl<A: Copy, F: Copy, S> Copy for MapSlice<A, F, S> {}
impl<A: Clone, F: Clone, S> Clone for MapSlice<A, F, S> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            mapper: self.mapper.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, S, A, F, O> Parser<'a, I, S> for MapSlice<A, F, S>
where
    I: Input + ?Sized,
    S: 'a,
    I::Slice: 'a,
    A: Parser<'a, I, S>,
    F: Fn(&'a I::Slice) -> O,
{
    type Output = O;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> Result<M::Output<Self::Output>, ()> {
        let before = inp.save();
        match self.parser.go::<Check>(inp) {
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

impl<'a, I, S, F> Parser<'a, I, S> for Filter<F, I>
where
    I: Input + ?Sized,
    S: 'a,
    F: Fn(&I::Token) -> bool,
{
    type Output = I::Token;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> Result<M::Output<Self::Output>, ()> {
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

impl<'a, I, S, A, F, O> Parser<'a, I, S> for Map<A, F>
where
    I: Input + ?Sized,
    S: 'a,
    A: Parser<'a, I, S>,
    F: Fn(A::Output) -> O,
{
    type Output = O;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> Result<M::Output<Self::Output>, ()> {
        self.parser.go::<M>(inp)
            .map(|out| M::map(out, &self.mapper))
    }

    go_extra!();
}

pub struct To<A, O, S = ()> {
    parser: A,
    to: O,
    phantom: PhantomData<S>,
}

impl<A: Copy, O: Copy, S> Copy for To<A, O, S> {}
impl<A: Clone, O: Clone, S> Clone for To<A, O, S> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            to: self.to.clone(),
            phantom: PhantomData,
        }
    }
}

impl<'a, I, S, A, O> Parser<'a, I, S> for To<A, O, S>
where
    I: Input + ?Sized,
    S: 'a,
    A: Parser<'a, I, S>,
    O: Clone,
{
    type Output = O;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> Result<M::Output<Self::Output>, ()> {
        self.parser.go::<Check>(inp)
            .map(|_| M::bind(|| self.to.clone()))
    }

    go_extra!();
}

pub type Ignored<A, S = ()> = To<A, (), S>;

#[derive(Copy, Clone)]
pub struct Then<A, B> {
    parser_a: A,
    parser_b: B,
}

impl<'a, I, S, A, B> Parser<'a, I, S> for Then<A, B>
where
    I: Input + ?Sized,
    S: 'a,
    A: Parser<'a, I, S>,
    B: Parser<'a, I, S>,
{
    type Output = (A::Output, B::Output);

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> Result<M::Output<Self::Output>, ()> {
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

impl<'a, I, S, A, B, C> Parser<'a, I, S> for DelimitedBy<A, B, C>
where
    I: Input + ?Sized,
    S: 'a,
    A: Parser<'a, I, S>,
    B: Parser<'a, I, S>,
    C: Parser<'a, I, S>,
{
    type Output = A::Output;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> Result<M::Output<Self::Output>, ()> {
        let _ = self.start.go::<Check>(inp)?;
        let b = self.parser.go::<M>(inp)?;
        let _ = self.end.go::<Check>(inp)?;
        Ok(b)
    }

    go_extra!();
}

#[derive(Copy, Clone)]
pub struct Or<A, B> {
    parser_a: A,
    parser_b: B,
}

impl<'a, I, S, A, B> Parser<'a, I, S> for Or<A, B>
where
    I: Input + ?Sized,
    S: 'a,
    A: Parser<'a, I, S>,
    B: Parser<'a, I, S, Output = A::Output>,
{
    type Output = A::Output;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> Result<M::Output<Self::Output>, ()> {
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
        impl<'a, I, S, $($X),*, O> Parser<'a, I, S> for Choice<($($X,)*), O>
        where
            I: Input + ?Sized,
            S: 'a,
            $($X: Parser<'a, I, S, Output = O>),*
        {
            type Output = O;

            fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> Result<M::Output<Self::Output>, ()> {
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

impl<'a, I, S, A> Parser<'a, I, S> for Padded<A>
where
    I: Input + ?Sized,
    S: 'a,
    I::Token: Char,
    A: Parser<'a, I, S>,
{
    type Output = A::Output;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> Result<M::Output<Self::Output>, ()> {
        inp.skip_while(|c| c.is_whitespace());
        let out = self.parser.go::<M>(inp)?;
        inp.skip_while(|c| c.is_whitespace());
        Ok(out)
    }

    go_extra!();
}

pub trait Container<T>: Default {
    fn push(&mut self, item: T);
}

impl<T> Container<T> for () {
    fn push(&mut self, _: T) {}
}

impl<T> Container<T> for Vec<T> {
    fn push(&mut self, item: T) {
        (*self).push(item);
    }
}

impl<K: Eq + Hash, V> Container<(K, V)> for HashMap<K, V> {
    fn push(&mut self, (key, value): (K, V)) {
        (*self).insert(key, value);
    }
}

pub struct Repeated<A, I: ?Sized, C = (), S = ()> {
    parser: A,
    at_least: usize,
    phantom: PhantomData<(C, S, I)>,
}

impl<A: Copy, I: ?Sized, C, S> Copy for Repeated<A, I, C, S> {}
impl<A: Copy, I: ?Sized, C, S> Clone for Repeated<A, I, C, S> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            at_least: self.at_least,
            phantom: PhantomData,
        }
    }
}

impl<'a, A: Parser<'a, I, S>, I: Input + ?Sized, C, S: 'a> Repeated<A, I, C, S> {
    pub fn at_least(self, at_least: usize) -> Self {
        Self { at_least, .. self }
    }

    pub fn collect<D: Container<A::Output>>(self) -> Repeated<A, I, D, S>
        where A: Parser<'a, I, S>
    {
        Repeated {
            parser: self.parser,
            at_least: self.at_least,
            phantom: PhantomData,
        }
    }
}

impl<'a, I, S, A, C> Parser<'a, I, S> for Repeated<A, I, C>
where
    I: Input + ?Sized,
    S: 'a,
    A: Parser<'a, I, S>,
    C: Container<A::Output>,
{
    type Output = C;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> Result<M::Output<Self::Output>, ()> {
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

impl<'a, I, S, A> Parser<'a, I, S> for OrNot<A>
where
    I: Input + ?Sized,
    S: 'a,
    A: Parser<'a, I, S>,
{
    type Output = Option<A::Output>;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> Result<M::Output<Self::Output>, ()> {
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

impl<'a, I, S, A, const N: usize> Parser<'a, I, S> for RepeatedExactly<A, N>
where
    I: Input + ?Sized,
    S: 'a,
    A: Parser<'a, I, S>,
{
    type Output = [A::Output; N];

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> Result<M::Output<Self::Output>, ()> {
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

pub struct RecursiveInner<'a, I: ?Sized, O, S = ()> {
    this: Rc<OnceCell<Self>>,
    parser: Box<dyn Parser<'a, I, S, Output = O> + 'a>,
}

pub struct Recursive<'a, I: ?Sized, O, S = ()> {
    inner: Rc<OnceCell<RecursiveInner<'a, I, O, S>>>,
}

impl<'a, I: ?Sized, O, S> Clone for Recursive<'a, I, O, S> {
    fn clone(&self) -> Self {
        Self { inner: self.inner.clone() }
    }
}

pub fn recursive<'a, I: Input + ?Sized, S, A: Parser<'a, I, S> + 'a, F: FnOnce(Recursive<'a, I, A::Output, S>) -> A>(f: F) -> Recursive<'a, I, A::Output, S> {
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

impl<'a, I, S, O> Parser<'a, I, S> for Recursive<'a, I, O, S>
where
    I: Input + ?Sized,
    S: 'a,
{
    type Output = O;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, S>) -> Result<M::Output<Self::Output>, ()> {
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
    let input = "🄯🄚🹠🴎🄐🝋🰏🄂🬯🈦g🸵🍩🕔🈳2🬙🨞🅢🭳🎅h🵚🧿🏩🰬k🠡🀔🈆🝹🤟🉗🴟📵🰄🤿🝜🙘🹄5🠻🡉🱖🠓";
    let mut state = ();
    let mut input = InputRef::new(input, &mut state);

    while let (_, Some(c)) = input.next() {
        std::hint::black_box(c);
    }
}
