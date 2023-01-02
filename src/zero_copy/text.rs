use crate::zero_copy::prelude::*;

use super::{primitive::{Any, Seq}, *};

pub trait Char: Sized + Copy + PartialEq {
    type Slice: ?Sized + StrInput<Self> + 'static;

    #[cfg(feature = "regex")]
    type Regex;

    #[cfg(feature = "regex")]
    #[doc(hidden)]
    fn new_regex(pattern: &str) -> Self::Regex;
    #[cfg(feature = "regex")]
    #[doc(hidden)]
    fn match_regex(regex: &Self::Regex, trailing: &Self::Slice) -> Option<usize>;

    /// Convert the given ASCII character to this character type.
    fn from_ascii(c: u8) -> Self;

    /// Returns true if the character is canonically considered to be inline whitespace (i.e: not part of a newline).
    fn is_inline_whitespace(&self) -> bool;

    /// Returns true if the character is canonically considered to be whitespace.
    fn is_whitespace(&self) -> bool;

    /// Return the '0' digit of the character.
    fn digit_zero() -> Self;

    /// Returns true if the character is canonically considered to be a numeric digit.
    fn is_digit(&self, radix: u32) -> bool;

    /// Returns this character as a [`char`].
    fn to_char(&self) -> char;
}

impl Char for char {
    type Slice = str;

    #[cfg(feature = "regex")]
    type Regex = ::regex::Regex;

    #[cfg(feature = "regex")]
    fn new_regex(pattern: &str) -> Self::Regex {
        ::regex::Regex::new(pattern).expect("Failed to compile regex")
    }
    #[cfg(feature = "regex")]
    #[inline]
    fn match_regex(regex: &Self::Regex, trailing: &Self::Slice) -> Option<usize> {
        regex
            .find(trailing)
            .filter(|m| m.start() == 0)
            .map(|m| m.end())
    }

    fn from_ascii(c: u8) -> Self {
        c as char
    }
    fn is_inline_whitespace(&self) -> bool {
        *self == ' ' || *self == '\t'
    }
    fn is_whitespace(&self) -> bool {
        char::is_whitespace(*self)
    }
    fn digit_zero() -> Self {
        '0'
    }
    fn is_digit(&self, radix: u32) -> bool {
        char::is_digit(*self, radix)
    }
    fn to_char(&self) -> char {
        *self
    }
}

impl Char for u8 {
    type Slice = [u8];

    #[cfg(feature = "regex")]
    type Regex = ::regex::bytes::Regex;

    #[cfg(feature = "regex")]
    fn new_regex(pattern: &str) -> Self::Regex {
        ::regex::bytes::Regex::new(pattern).expect("Failed to compile regex")
    }
    #[cfg(feature = "regex")]
    #[inline]
    fn match_regex(regex: &Self::Regex, trailing: &Self::Slice) -> Option<usize> {
        regex
            .find(trailing)
            .filter(|m| m.start() == 0)
            .map(|m| m.end())
    }

    fn from_ascii(c: u8) -> Self {
        c
    }
    fn is_inline_whitespace(&self) -> bool {
        *self == b' ' || *self == b'\t'
    }
    fn is_whitespace(&self) -> bool {
        self.is_ascii_whitespace()
    }
    fn digit_zero() -> Self {
        b'0'
    }
    fn is_digit(&self, radix: u32) -> bool {
        (*self as char).is_digit(radix)
    }
    fn to_char(&self) -> char {
        *self as char
    }
}

#[derive(Clone)]
pub struct Padded<A> {
    pub(crate) parser: A,
}

impl<'a, I, O, E, S, A> Parser<'a, I, O, E, S> for Padded<A>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    I::Token: Char,
    A: Parser<'a, I, O, E, S>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, O, E> {
        inp.skip_while(|c| c.is_whitespace());
        let out = self.parser.go::<M>(inp)?;
        inp.skip_while(|c| c.is_whitespace());
        Ok(out)
    }

    go_extra!(O);
}

/// A parser that accepts (and ignores) any number of whitespace characters.
///
/// This parser is a `Parser::Repeated` and so methods such as `at_least()` can be called on it.
///
/// The output type of this parser is `Vec<()>`.
///
/// # Examples
///
/// ```
/// # use chumsky::prelude::*;
/// let whitespace = text::whitespace::<_, Simple<char>>();
///
/// // Any amount of whitespace is parsed...
/// assert_eq!(whitespace.parse("\t \n  \r "), Ok(vec![(), (), (), (), (), (), ()]));
/// // ...including none at all!
/// assert_eq!(whitespace.parse(""), Ok(vec![]));
/// ```
pub fn whitespace<'a, I: Input, E: Error<I>>(
) -> Repeated<Filter<Any<I, E>, impl Fn(&I::Token) -> bool>, I::Token, I, (), E> 
where
    I::Token: Char,
{
    any().filter(|c: &I::Token| c.is_whitespace()).repeated()
}


/// A parser that accepts (and ignores) any newline characters or character sequences.
///
/// The output type of this parser is `()`.
///
/// This parser is quite extensive, recognising:
///
/// - Line feed (`\n`)
/// - Carriage return (`\r`)
/// - Carriage return + line feed (`\r\n`)
/// - Vertical tab (`\x0B`)
/// - Form feed (`\x0C`)
/// - Next line (`\u{0085}`)
/// - Line separator (`\u{2028}`)
/// - Paragraph separator (`\u{2029}`)
///
/// # Examples
///
/// ```
/// # use chumsky::prelude::*;
/// let newline = text::newline::<char, Simple<char>>()
///     .then_ignore(end());
///
/// assert_eq!(newline.parse("\n"), Ok(()));
/// assert_eq!(newline.parse("\r"), Ok(()));
/// assert_eq!(newline.parse("\r\n"), Ok(()));
/// assert_eq!(newline.parse("\x0B"), Ok(()));
/// assert_eq!(newline.parse("\x0C"), Ok(()));
/// assert_eq!(newline.parse("\u{0085}"), Ok(()));
/// assert_eq!(newline.parse("\u{2028}"), Ok(()));
/// assert_eq!(newline.parse("\u{2029}"), Ok(()));
/// ```
#[must_use]
pub fn newline<'a, I: Input + ?Sized, E: Error<I> + 'a>(
) -> impl Parser<'a, I, (), E> 
where
    I::Token: Char
{
    just(I::Token::from_ascii(b'\r'))
        .or_not()
        .ignore_then(just(I::Token::from_ascii(b'\n')))
        .or(any().filter(|c: &I::Token| {
            [
                '\r',       // Carriage return
                '\x0B',     // Vertical tab
                '\x0C',     // Form feed
                '\u{0085}', // Next line
                '\u{2028}', // Line separator
                '\u{2029}', // Paragraph separator
            ]
            .contains(&c.to_char())
        }))
        .ignored()
}

/// A parser that accepts one or more ASCII digits.
///
/// The output type of this parser is [`Character::Collection`] (i.e: [`String`] when `C` is [`char`], and [`Vec<u8>`]
/// when `C` is [`u8`]).
///
/// The `radix` parameter functions identically to [`char::is_digit`]. If in doubt, choose `10`.
///
/// # Examples
///
/// ```
/// # use chumsky::prelude::*;
/// let digits = text::digits::<_, Simple<char>>(10);
///
/// assert_eq!(digits.parse("0"), Ok("0".to_string()));
/// assert_eq!(digits.parse("1"), Ok("1".to_string()));
/// assert_eq!(digits.parse("01234"), Ok("01234".to_string()));
/// assert_eq!(digits.parse("98345"), Ok("98345".to_string()));
/// // A string of zeroes is still valid. Use `int` if this is not desirable.
/// assert_eq!(digits.parse("0000"), Ok("0000".to_string()));
/// assert!(digits.parse("").is_err());
/// ```
#[must_use]
pub fn digits<'a, I: StrInput<C>, C: Char, E: Error<I>>(
    radix: u32,
) -> impl Parser<'a, I, &'a C::Slice, E> + Copy + Clone 
{
    any().filter(move |c: &C| c.is_digit(radix))
        .repeated()
        .at_least(1)
        .map_slice(|x| x)
}

/// A parser that accepts a non-negative integer.
///
/// An integer is defined as a non-empty sequence of ASCII digits, where the first digit is non-zero or the sequence
/// has length one.
///
/// The output type of this parser is [`Character::Collection`] (i.e: [`String`] when `C` is [`char`], and [`Vec<u8>`]
/// when `C` is [`u8`]).
///
/// The `radix` parameter functions identically to [`char::is_digit`]. If in doubt, choose `10`.
///
/// # Examples
///
/// ```
/// # use chumsky::prelude::*;
/// let dec = text::int::<_, Simple<char>>(10)
///     .then_ignore(end());
///
/// assert_eq!(dec.parse("0"), Ok("0".to_string()));
/// assert_eq!(dec.parse("1"), Ok("1".to_string()));
/// assert_eq!(dec.parse("1452"), Ok("1452".to_string()));
/// // No leading zeroes are permitted!
/// assert!(dec.parse("04").is_err());
///
/// let hex = text::int::<_, Simple<char>>(16)
///     .then_ignore(end());
///
/// assert_eq!(hex.parse("2A"), Ok("2A".to_string()));
/// assert_eq!(hex.parse("d"), Ok("d".to_string()));
/// assert_eq!(hex.parse("b4"), Ok("b4".to_string()));
/// assert!(hex.parse("0B").is_err());
/// ```
#[must_use]
pub fn int<'a, I: StrInput<C> + ?Sized, C: Char, E: Error<I>>(
    radix: u32,
) -> impl Parser<'a, I, &'a C::Slice, E>
{
    any().filter(move |c: &C| c.is_digit(radix) && c != &C::digit_zero())
        .map(Some)
        .then(any().filter(move |c: &C| c.is_digit(radix)).repeated())
        .ignored()
        .or(just(C::digit_zero()).ignored())
        .map_slice(|x| x)
}

/// A parser that accepts a C-style identifier.
///
/// The output type of this parser is [`Character::Collection`] (i.e: [`String`] when `C` is [`char`], and [`Vec<u8>`]
/// when `C` is [`u8`]).
///
/// An identifier is defined as an ASCII alphabetic character or an underscore followed by any number of alphanumeric
/// characters or underscores. The regex pattern for it is `[a-zA-Z_][a-zA-Z0-9_]*`.
#[must_use]
pub fn ident<'a, I: StrInput<C> + ?Sized, C: Char, E: Error<I>>() -> impl Parser<'a, I, &'a C::Slice, E>
{
    any().filter(|c: &C| c.to_char().is_ascii_alphabetic() || c.to_char() == '_')
        .then(
            any().filter(|c: &C| c.to_char().is_ascii_alphanumeric() || c.to_char() == '_').repeated()
        )
        .map_slice(|x| x)
}

/// Like [`ident`], but only accepts an exact identifier while ignoring trailing identifier characters.
///
/// The output type of this parser is `()`.
///
/// # Examples
///
/// ```
/// # use chumsky::prelude::*;
/// let def = text::keyword::<_, _, Simple<char>>("def");
///
/// // Exactly 'def' was found
/// assert_eq!(def.parse("def"), Ok(()));
/// // Exactly 'def' was found, with non-identifier trailing characters
/// assert_eq!(def.parse("def(foo, bar)"), Ok(()));
/// // 'def' was found, but only as part of a larger identifier, so this fails to parse
/// assert!(def.parse("define").is_err());
/// ```
#[must_use]
pub fn keyword<'a, K: Seq<C> + 'a, I: StrInput<C>, C: Char, E: Error<I> + 'a>(
    keyword: &'a K,
) -> impl Parser<'a, I, (), E>
where &'a K: Seq<C>
{
    ident().ignored().and_is(just(keyword)).ignored()
}


/// A parser that consumes text and generates tokens using semantic whitespace rules and the given token parser.
///
/// Also required is a function that collects a [`Vec`] of tokens into a whitespace-indicated token tree.
#[must_use]
pub fn semantic_indentation<'a, Tok, T, F, E: Error<str> + 'a>(
    token: T,
    make_group: F,
) -> impl Parser<'a, str, Vec<Tok>, E> + 'a
where
    Tok: Clone + 'a,
    T: Parser<'a, str, Tok, E> + Clone + 'a,
    F: Fn(Vec<Tok>, Range<usize>) -> Tok + Clone + 'a,
{
    let line_ws = any::<str, E, _>().filter(|c: &char| c.is_inline_whitespace());

    let line = token
        .padded_by(line_ws.repeated())
        .repeated()
        .collect::<Vec<_>>();

    let lines = line_ws
        .repeated()
        .map_slice(|x| x)
        .then(
            line.collect::<Vec<_>>()
                .map_with_span(|line, span| (line, span)),
        )
        .then_ignore(line_ws.repeated())
        .separated_by(newline())
        .collect();

    lines.map(move |lines: Vec<(&str, (Vec<Tok>, Range<usize>))>| {
        fn collapse<'b, Tok, F>(
            mut tree: Vec<(&'b str, Vec<Tok>, Option<Range<usize>>)>,
            make_group: &F,
        ) -> Option<Tok>
        where
            F: Fn(Vec<Tok>, Range<usize>) -> Tok,
        {
            while let Some((_, tts, line_span)) = tree.pop() {
                let tt = make_group(tts, line_span?);
                if let Some(last) = tree.last_mut() {
                    last.1.push(tt);
                } else {
                    return Some(tt);
                }
            }
            None
        }

        let mut nesting = vec![("", Vec::new(), None)];
        for (mut indent, (mut line, line_span)) in lines {
            let mut i = 0;
            while let Some(tail) = nesting
                .get(i)
                .and_then(|(n, _, _)| indent.strip_prefix(n))
            {
                indent = tail;
                i += 1;
            }
            if let Some(tail) = collapse(nesting.split_off(i), &make_group) {
                nesting.last_mut().unwrap().1.push(tail);
            }
            if !indent.is_empty() {
                nesting.push((indent, line, Some(line_span)));
            } else {
                nesting.last_mut().unwrap().1.append(&mut line);
            }
        }

        nesting.remove(0).1
    })
}
