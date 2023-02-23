//! Text-specific parsers and utilities.
//!
//! *“Ford!" he said, "there's an infinite number of monkeys outside who want to talk to us about this script for
//! Hamlet they've worked out.”*
//!
//! The parsers in this module are generic over both Unicode ([`char`]) and ASCII ([`u8`]) characters. Most parsers take
//! a type parameter, `C`, that can be either [`u8`] or [`char`] in order to handle either case.
//!
//! The [`TextParser`] trait is an extension on top of the main [`Parser`] trait that adds combinators unique to the
//! parsing of text.

use crate::zero_copy::prelude::*;

use super::*;

/// A trait implemented by textual character types (currently, [`u8`] and [`char`]).
///
/// Avoid implementing this trait yourself if you can: it's *very* likely to be expanded in future versions!
pub trait Char: Sized + Copy + PartialEq {
    /// The default unsized [`str`]-like type of a linear sequence of this character.
    ///
    /// For [`char`], this is [`str`]. For [`u8`], this is [`[u8]`].
    type Str: ?Sized + 'static;

    /// The type of a regex expression which can match on this type
    #[cfg(feature = "regex")]
    type Regex;

    #[cfg(feature = "regex")]
    #[doc(hidden)]
    fn new_regex(pattern: &str) -> Self::Regex;
    #[cfg(feature = "regex")]
    #[doc(hidden)]
    fn match_regex(regex: &Self::Regex, trailing: &Self::Str) -> Option<usize>;

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
    type Str = str;

    #[cfg(feature = "regex")]
    type Regex = ::regex::Regex;

    #[cfg(feature = "regex")]
    fn new_regex(pattern: &str) -> Self::Regex {
        ::regex::Regex::new(pattern).expect("Failed to compile regex")
    }
    #[cfg(feature = "regex")]
    #[inline]
    fn match_regex(regex: &Self::Regex, trailing: &Self::Str) -> Option<usize> {
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
    type Str = [u8];

    #[cfg(feature = "regex")]
    type Regex = ::regex::bytes::Regex;

    #[cfg(feature = "regex")]
    fn new_regex(pattern: &str) -> Self::Regex {
        ::regex::bytes::Regex::new(pattern).expect("Failed to compile regex")
    }
    #[cfg(feature = "regex")]
    #[inline]
    fn match_regex(regex: &Self::Regex, trailing: &Self::Str) -> Option<usize> {
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

/// A parser that accepts (and ignores) any number of whitespace characters before or after another pattern.
#[derive(Copy, Clone)]
pub struct Padded<A> {
    pub(crate) parser: A,
}

impl<'a, I, O, E, A> Parser<'a, I, O, E> for Padded<A>
where
    I: Input<'a>,
    E: ParserExtra<'a, I>,
    I::Token: Char,
    A: Parser<'a, I, O, E>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O, E::Error> {
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
/// The output type of this parser is `()`.
///
/// # Examples
///
/// ```
/// # use chumsky::zero_copy::prelude::*;
/// let whitespace = text::whitespace::<_, _, extra::Err<Simple<&str>>>();
///
/// // Any amount of whitespace is parsed...
/// assert_eq!(whitespace.parse("\t \n  \r ").into_result(), Ok(()));
/// // ...including none at all!
/// assert_eq!(whitespace.parse("").into_result(), Ok(()));
/// ```
pub fn whitespace<'a, C: Char, I: StrInput<'a, C>, E: ParserExtra<'a, I>>(
) -> Repeated<impl Parser<'a, I, (), E> + Copy + Clone, (), I, E>
where
    I::Token: Char,
{
    any()
        .filter(|c: &I::Token| c.is_whitespace())
        .ignored()
        .repeated()
}

/// A parser that accepts (and ignores) any number of inline whitespace characters.
///
/// This parser is a `Parser::Repeated` and so methods such as `at_least()` can be called on it.
///
/// The output type of this parser is `()`.
///
/// # Examples
///
/// ```
/// # use chumsky::zero_copy::prelude::*;
/// let inline_whitespace = text::inline_whitespace::<_, _, extra::Err<Simple<&str>>>();
///
/// // Any amount of inline whitespace is parsed...
/// assert_eq!(inline_whitespace.parse("\t  ").into_result(), Ok(()));
/// // ...including none at all!
/// assert_eq!(inline_whitespace.parse("").into_result(), Ok(()));
/// // ... but not newlines
/// assert!(inline_whitespace.at_least(1).parse("\n\r").has_errors());
/// ```
pub fn inline_whitespace<'a, C: Char, I: StrInput<'a, C>, E: ParserExtra<'a, I>>(
) -> Repeated<impl Parser<'a, I, (), E> + Copy + Clone, (), I, E>
where
    I::Token: Char,
{
    any()
        .filter(|c: &I::Token| c.is_inline_whitespace())
        .ignored()
        .repeated()
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
/// # use chumsky::zero_copy::prelude::*;
/// let newline = text::newline::<_, extra::Err<Simple<&str>>>();
///
/// assert_eq!(newline.parse("\n").into_result(), Ok(()));
/// assert_eq!(newline.parse("\r").into_result(), Ok(()));
/// assert_eq!(newline.parse("\r\n").into_result(), Ok(()));
/// assert_eq!(newline.parse("\x0B").into_result(), Ok(()));
/// assert_eq!(newline.parse("\x0C").into_result(), Ok(()));
/// assert_eq!(newline.parse("\u{0085}").into_result(), Ok(()));
/// assert_eq!(newline.parse("\u{2028}").into_result(), Ok(()));
/// assert_eq!(newline.parse("\u{2029}").into_result(), Ok(()));
/// ```
#[must_use]
pub fn newline<'a, I: Input<'a>, E: ParserExtra<'a, I>>() -> impl Parser<'a, I, (), E> + Copy + Clone
where
    I::Token: Char,
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
/// The output type of this parser is `I::Slice` (i.e: [`&str`] when `I` is [`&str`], and [`&[u8]`]
/// when `I::Slice` is [`&[u8]`]).
///
/// The `radix` parameter functions identically to [`char::is_digit`]. If in doubt, choose `10`.
///
/// # Examples
///
/// ```
/// # use chumsky::zero_copy::prelude::*;
/// let digits = text::digits::<'_, _, _, extra::Err<Simple<&str>>>(10).slice();
///
/// assert_eq!(digits.parse("0").into_result(), Ok("0"));
/// assert_eq!(digits.parse("1").into_result(), Ok("1"));
/// assert_eq!(digits.parse("01234").into_result(), Ok("01234"));
/// assert_eq!(digits.parse("98345").into_result(), Ok("98345"));
/// // A string of zeroes is still valid. Use `int` if this is not desirable.
/// assert_eq!(digits.parse("0000").into_result(), Ok("0000"));
/// assert!(digits.parse("").has_errors());
/// ```
#[must_use]
pub fn digits<'a, C, I, E>(radix: u32) -> Repeated<impl Parser<'a, I, C, E> + Copy + Clone, C, I, E>
where
    C: Char,
    I: StrInput<'a, C>,
    E: ParserExtra<'a, I>,
{
    any()
        .filter(move |c: &C| c.is_digit(radix))
        .repeated()
        .at_least(1)
}

/// A parser that accepts a non-negative integer.
///
/// An integer is defined as a non-empty sequence of ASCII digits, where the first digit is non-zero or the sequence
/// has length one.
///
/// The output type of this parser is `I::Slice` (i.e: [`&str`] when `I` is [`&str`], and [`&[u8]`]
/// when `I::Slice` is [`&[u8]`]).
///
/// The `radix` parameter functions identically to [`char::is_digit`]. If in doubt, choose `10`.
///
/// # Examples
///
/// ```
/// # use chumsky::zero_copy::prelude::*;
/// let dec = text::int::<_, _, extra::Err<Simple<&str>>>(10);
///
/// assert_eq!(dec.parse("0").into_result(), Ok("0"));
/// assert_eq!(dec.parse("1").into_result(), Ok("1"));
/// assert_eq!(dec.parse("1452").into_result(), Ok("1452"));
/// // No leading zeroes are permitted!
/// assert!(dec.parse("04").has_errors());
///
/// let hex = text::int::<_, _, extra::Err<Simple<&str>>>(16);
///
/// assert_eq!(hex.parse("2A").into_result(), Ok("2A"));
/// assert_eq!(hex.parse("d").into_result(), Ok("d"));
/// assert_eq!(hex.parse("b4").into_result(), Ok("b4"));
/// assert!(hex.parse("0B").has_errors());
/// ```
///
#[must_use]
pub fn int<'a, I: StrInput<'a, C>, C: Char, E: ParserExtra<'a, I>>(
    radix: u32,
) -> impl Parser<'a, I, &'a C::Str, E> + Copy + Clone {
    any()
        .filter(move |c: &C| c.is_digit(radix) && c != &C::digit_zero())
        .map(Some)
        .then(any().filter(move |c: &C| c.is_digit(radix)).repeated())
        .ignored()
        .or(just(C::digit_zero()).ignored())
        .slice()
}

/// A parser that accepts a C-style identifier.
///
/// The output type of this parser is [`Character::Collection`] (i.e: [`String`] when `C` is [`char`], and [`Vec<u8>`]
/// when `C` is [`u8`]).
///
/// An identifier is defined as an ASCII alphabetic character or an underscore followed by any number of alphanumeric
/// characters or underscores. The regex pattern for it is `[a-zA-Z_][a-zA-Z0-9_]*`.
#[must_use]
pub fn ident<'a, I: StrInput<'a, C>, C: Char, E: ParserExtra<'a, I>>(
) -> impl Parser<'a, I, &'a C::Str, E> + Copy + Clone {
    any()
        .filter(|c: &C| c.to_char().is_ascii_alphabetic() || c.to_char() == '_')
        .then(
            any()
                .filter(|c: &C| c.to_char().is_ascii_alphanumeric() || c.to_char() == '_')
                .repeated(),
        )
        .slice()
}

/// A parser that consumes text and generates tokens using semantic whitespace rules and the given token parser.
///
/// Also required is a function that collects a [`Vec`] of tokens into a whitespace-indicated token tree.
#[must_use]
pub fn semantic_indentation<'a, Tok, T, F, E: ParserExtra<'a, &'a str>>(
    token: T,
    make_group: F,
) -> impl Parser<'a, &'a str, Vec<Tok>, E>
where
    T: Parser<'a, &'a str, Tok, E>,
    F: Fn(Vec<Tok>, SimpleSpan<usize>) -> Tok,
{
    let line_ws = any::<&'a str, E>().filter(|c: &char| c.is_inline_whitespace());

    let line = token
        .padded_by(line_ws.repeated())
        .repeated()
        .collect::<Vec<_>>();

    let lines = line_ws
        .repeated()
        .slice()
        .then(line.map_with_span(|line, span| (line, span)))
        .then_ignore(line_ws.repeated())
        .separated_by(newline())
        .collect();

    lines.map(move |lines: Vec<(&str, (Vec<Tok>, SimpleSpan<usize>))>| {
        fn collapse<'b, Tok, F>(
            mut tree: Vec<(&'b str, Vec<Tok>, Option<SimpleSpan<usize>>)>,
            make_group: &F,
        ) -> Option<Tok>
        where
            F: Fn(Vec<Tok>, SimpleSpan<usize>) -> Tok,
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
            while let Some(tail) = nesting.get(i).and_then(|(n, _, _)| indent.strip_prefix(n)) {
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

/// Like [`ident`], but only accepts a specific identifier while rejecting trailing identifier characters.
///
/// The output type of this parser is `I::Slice` (i.e: [`&str`] when `I` is [`&str`], and [`&[u8]`]
/// when `I::Slice` is [`&[u8]`]).
///
/// # Examples
///
/// ```
/// # use chumsky::zero_copy::prelude::*;
/// let def = text::keyword::<_, _, _, extra::Err<Simple<&str>>>("def");
///
/// // Exactly 'def' was found
/// assert_eq!(def.parse("def").into_result(), Ok("def"));
/// // Exactly 'def' was found, with non-identifier trailing characters
/// // This works because we made the parser lazy: it parses 'def' and ignores the rest
/// assert_eq!(def.clone().lazy().parse("def(foo, bar)").into_result(), Ok("def"));
/// // 'def' was found, but only as part of a larger identifier, so this fails to parse
/// assert!(def.lazy().parse("define").has_errors());
/// ```
pub fn keyword<
    'a,
    I: StrInput<'a, C>,
    C: Char + 'a,
    Str: AsRef<C::Str> + 'a + Clone,
    E: ParserExtra<'a, I> + 'a,
>(
    keyword: Str,
) -> impl Parser<'a, I, &'a C::Str, E> + Clone + 'a
where
    C::Str: PartialEq,
{
    // TODO: use .filter(...), improve error messages
    ident()
        .try_map(move |s: &C::Str, span| {
            if s == keyword.as_ref() {
                Ok(())
            } else {
                Err(E::Error::expected_found(None, None, span))
            }
        })
        .slice()
}
