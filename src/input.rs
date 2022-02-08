//! Input streams and values.

use core::{
    borrow::Borrow,
    ops::{Range, RangeFrom},
    marker::PhantomData,
};

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

struct InputRef<'a, I: Input + ?Sized> {
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

trait Parser<'a, I: Input + ?Sized>: Sized {
    type Output;

    fn parse(&self, input: &'a I) -> Result<Self::Output, ()> {
        self.go(&mut InputRef::new(input))
    }

    #[doc(hidden)]
    fn go(&self, inp: &mut InputRef<'a, I>) -> Result<Self::Output, ()>;

    fn map_slice<O, F: Fn(&'a I::Slice) -> O>(self, f: F) -> MapSlice<Self, F>
    where
        I::Slice: 'a,
    {
        MapSlice { parser: self, mapper: f }
    }

    fn map<O, F: Fn(Self::Output) -> O>(self, f: F) -> Map<Self, F> {
        Map { parser: self, mapper: f }
    }

    fn then<B: Parser<'a, I>>(self, other: B) -> Then<Self, B> {
        Then { parser_a: self, parser_b: other }
    }

    fn or<B: Parser<'a, I, Output = Self::Output>>(self, other: B) -> Or<Self, B> {
        Or { parser_a: self, parser_b: other }
    }

    fn repeated(self) -> Repeated<Self> {
        Repeated { parser: self, at_least: 0 }
    }

    fn padded(self) -> Padded<Self> where I: Input<Token = char> {
        Padded { parser: self }
    }
}

#[derive(Copy, Clone)]
pub struct Just<T, I: ?Sized>(T, PhantomData<I>);

pub fn just<T: PartialEq<I::Token>, I: Input + ?Sized>(tok: T) -> Just<T, I> {
    Just(tok, PhantomData)
}

impl<'a, I, T> Parser<'a, I> for Just<T, I>
where
    I: Input + ?Sized,
    T: PartialEq<I::Token>,
{
    type Output = I::Token;

    fn go(&self, inp: &mut InputRef<'a, I>) -> Result<Self::Output, ()> {
        match inp.next() {
            (_, Some(tok)) if self.0 == tok => Ok(tok),
            (_, Some(_) | None) => Err(()),
        }
    }
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

    fn go(&self, inp: &mut InputRef<'a, I>) -> Result<Self::Output, ()> {
        let before = inp.save();
        match self.parser.go(inp) {
            Ok(_) => {
                let after = inp.save();
                Ok((self.mapper)(inp.slice(before..after)))
            },
            Err(e) => Err(e),
        }
    }
}

#[derive(Copy, Clone)]
pub struct Filter<F, I: ?Sized> {
    filter: F,
    phantom: PhantomData<I>,
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

    fn go(&self, inp: &mut InputRef<'a, I>) -> Result<Self::Output, ()> {
        match inp.next() {
            (_, Some(tok)) if (self.filter)(&tok) => Ok(tok),
            (_, Some(_) | None) => Err(()),
        }
    }
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

    fn go(&self, inp: &mut InputRef<'a, I>) -> Result<Self::Output, ()> {
        self.parser.go(inp).map(&self.mapper)
    }
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

    fn go(&self, inp: &mut InputRef<'a, I>) -> Result<Self::Output, ()> {
        let a = self.parser_a.go(inp)?;
        let b = self.parser_b.go(inp)?;
        Ok((a, b))
    }
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

    fn go(&self, inp: &mut InputRef<'a, I>) -> Result<Self::Output, ()> {
        let before = inp.save();
        match self.parser_a.go(inp) {
            Ok(out) => Ok(out),
            Err(()) => {
                inp.rewind(before);
                self.parser_b.go(inp)
            },
        }
    }
}

#[derive(Clone)]
pub struct Padded<A> {
    parser: A,
}

impl<'a, I, A> Parser<'a, I> for Padded<A>
where
    I: Input<Token = char> + ?Sized,
    A: Parser<'a, I>,
{
    type Output = A::Output;

    fn go(&self, inp: &mut InputRef<'a, I>) -> Result<Self::Output, ()> {
        inp.skip_while(|c| c.is_whitespace());
        let out = self.parser.go(inp)?;
        inp.skip_while(|c| c.is_whitespace());
        Ok(out)
    }
}

#[derive(Copy, Clone)]
pub struct Repeated<A> {
    parser: A,
    at_least: usize,
}

impl<A> Repeated<A> {
    pub fn at_least(self, at_least: usize) -> Self {
        Self { at_least, .. self }
    }
}

impl<'a, I, A> Parser<'a, I> for Repeated<A>
where
    I: Input + ?Sized,
    A: Parser<'a, I>,
{
    type Output = Vec<A::Output>;

    fn go(&self, inp: &mut InputRef<'a, I>) -> Result<Self::Output, ()> {
        let mut output = Vec::new();
        loop {
            let before = inp.save();
            match self.parser.go(inp) {
                Ok(out) => output.push(out),
                Err(()) => {
                    inp.rewind(before);
                    break if output.len() >= self.at_least {
                        Ok(output)
                    } else {
                        Err(())
                    };
                },
            }
        }
    }
}

#[test]
fn zero_copy() {
    #[derive(PartialEq, Debug)]
    enum Token<'a> {
        Ident(&'a str),
        String(&'a str),
    }

    fn parser<'a>() -> impl Parser<'a, str, Output = Vec<Token<'a>>> {
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
            .repeated()
    }

    assert_eq!(
        parser().parse(r#"hello "world" these are "test" tokens"#),
        Ok(vec![
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
