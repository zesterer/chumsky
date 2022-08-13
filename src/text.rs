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

use super::*;
use core::iter::FromIterator;

/// The type of a parser that accepts (and ignores) any number of whitespace characters.
pub type Padding<I, E> = Custom<fn(&mut StreamOf<I, E>) -> PResult<I, (), E>, E>;

/// The type of a parser that accepts (and ignores) any number of whitespace characters before or after another
/// pattern.
// pub type Padded<P, I, O> = ThenIgnore<
//     IgnoreThen<Padding<I, <P as Parser<I, O>>::Error>, P, (), O>,
//     Padding<I, <P as Parser<I, O>>::Error>,
//     O,
//     (),
// >;

/// A parser that accepts (and ignores) any number of whitespace characters before or after another pattern.
#[must_use]
#[derive(Copy, Clone)]
pub struct Padded<A>(A);

impl<C: Character, O, A: Parser<C, O, Error = E>, E: Error<C>> Parser<C, O> for Padded<A> {
    type Error = E;

    #[inline]
    fn parse_inner<D: Debugger>(
        &self,
        debugger: &mut D,
        stream: &mut StreamOf<C, E>,
    ) -> PResult<C, O, E> {
        while stream.skip_if(|c| c.is_whitespace()) {}
        match self.0.parse_inner(debugger, stream) {
            (a_errors, Ok((a_out, a_alt))) => {
                while stream.skip_if(|c| c.is_whitespace()) {}
                (a_errors, Ok((a_out, a_alt)))
            }
            (a_errors, Err(err)) => (a_errors, Err(err)),
        }
    }

    #[inline]
    fn parse_inner_verbose(&self, d: &mut Verbose, s: &mut StreamOf<C, E>) -> PResult<C, O, E> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
    #[inline]
    fn parse_inner_silent(&self, d: &mut Silent, s: &mut StreamOf<C, E>) -> PResult<C, O, E> {
        #[allow(deprecated)]
        self.parse_inner(d, s)
    }
}

mod private {
    pub trait Sealed {}

    impl Sealed for u8 {}
    impl Sealed for char {}
}

/// A trait implemented by textual character types (currently, [`u8`] and [`char`]).
///
/// Avoid implementing this trait yourself if you can: it's *very* likely to be expanded in future versions!
pub trait Character: private::Sealed + Copy + PartialEq {
    /// The default unsized [`str`]-like type of a linear sequence of this character.
    ///
    /// For [`char`], this is [`str`]. For [`u8`], this is [`[u8]`].
    type Str: ?Sized + PartialEq;

    /// The default type that this character collects into.
    ///
    /// For [`char`], this is [`String`]. For [`u8`], this is [`Vec<u8>`].
    type Collection: Chain<Self> + FromIterator<Self> + AsRef<Self::Str> + 'static;

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

impl Character for u8 {
    type Str = [u8];
    type Collection = Vec<u8>;

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

impl Character for char {
    type Str = str;
    type Collection = String;

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

/// A trait containing text-specific functionality that extends the [`Parser`] trait.
pub trait TextParser<I: Character, O>: Parser<I, O> {
    /// Parse a pattern, ignoring any amount of whitespace both before and after the pattern.
    ///
    /// The output type of this parser is `O`, the same as the original parser.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// let ident = text::ident::<_, Simple<char>>().padded();
    ///
    /// // A pattern with no whitespace surrounding it is accepted
    /// assert_eq!(ident.parse("hello"), Ok("hello".to_string()));
    /// // A pattern with arbitrary whitespace surrounding it is also accepted
    /// assert_eq!(ident.parse(" \t \n  \t   world  \t  "), Ok("world".to_string()));
    /// ```
    fn padded(self) -> Padded<Self>
    where
        Self: Sized,
    {
        Padded(self)
        // whitespace().ignore_then(self).then_ignore(whitespace())
    }
}

impl<I: Character, O, P: Parser<I, O>> TextParser<I, O> for P {}

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
pub fn whitespace<'a, C: Character + 'a, E: Error<C> + 'a>(
) -> Repeated<impl Parser<C, (), Error = E> + Copy + Clone + 'a> {
    filter(|c: &C| c.is_whitespace()).ignored().repeated()
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
pub fn newline<'a, C: Character + 'a, E: Error<C> + 'a>(
) -> impl Parser<C, (), Error = E> + Copy + Clone + 'a {
    just(C::from_ascii(b'\r'))
        .or_not()
        .ignore_then(just(C::from_ascii(b'\n')))
        .or(filter(|c: &C| {
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
pub fn digits<C: Character, E: Error<C>>(
    radix: u32,
) -> impl Parser<C, C::Collection, Error = E> + Copy + Clone {
    filter(move |c: &C| c.is_digit(radix))
        .repeated()
        .at_least(1)
        .collect()
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
pub fn int<C: Character, E: Error<C>>(
    radix: u32,
) -> impl Parser<C, C::Collection, Error = E> + Copy + Clone {
    filter(move |c: &C| c.is_digit(radix) && c != &C::digit_zero())
        .map(Some)
        .chain::<C, Vec<_>, _>(filter(move |c: &C| c.is_digit(radix)).repeated())
        .collect()
        .or(just(C::digit_zero()).map(|c| core::iter::once(c).collect()))
}

/// A parser that accepts a C-style identifier.
///
/// The output type of this parser is [`Character::Collection`] (i.e: [`String`] when `C` is [`char`], and [`Vec<u8>`]
/// when `C` is [`u8`]).
///
/// An identifier is defined as an ASCII alphabetic character or an underscore followed by any number of alphanumeric
/// characters or underscores. The regex pattern for it is `[a-zA-Z_][a-zA-Z0-9_]*`.
#[must_use]
pub fn ident<C: Character, E: Error<C>>() -> impl Parser<C, C::Collection, Error = E> + Copy + Clone
{
    filter(|c: &C| c.to_char().is_ascii_alphabetic() || c.to_char() == '_')
        .map(Some)
        .chain::<C, Vec<_>, _>(
            filter(|c: &C| c.to_char().is_ascii_alphanumeric() || c.to_char() == '_').repeated(),
        )
        .collect()
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
pub fn keyword<'a, C: Character + 'a, S: AsRef<C::Str> + 'a + Clone, E: Error<C> + 'a>(
    keyword: S,
) -> impl Parser<C, (), Error = E> + Clone + 'a {
    // TODO: use .filter(...), improve error messages
    ident().try_map(move |s: C::Collection, span| {
        if s.as_ref() == keyword.as_ref() {
            Ok(())
        } else {
            Err(E::expected_input_found(span, None, None))
        }
    })
}

/// A parser that consumes text and generates tokens using semantic whitespace rules and the given token parser.
///
/// Also required is a function that collects a [`Vec`] of tokens into a whitespace-indicated token tree.
#[must_use]
pub fn semantic_indentation<'a, C, Tok, T, F, E: Error<C> + 'a>(
    token: T,
    make_group: F,
) -> impl Parser<C, Vec<Tok>, Error = E> + Clone + 'a
where
    C: Character + 'a,
    Tok: 'a,
    T: Parser<C, Tok, Error = E> + Clone + 'a,
    F: Fn(Vec<Tok>, E::Span) -> Tok + Clone + 'a,
{
    let line_ws = filter(|c: &C| c.is_inline_whitespace());

    let line = token.padded_by(line_ws.ignored().repeated()).repeated();

    let lines = line_ws
        .repeated()
        .then(line.map_with_span(|line, span| (line, span)))
        .separated_by(newline())
        .padded();

    lines.map(move |lines| {
        fn collapse<C, Tok, F, S>(
            mut tree: Vec<(Vec<C>, Vec<Tok>, Option<S>)>,
            make_group: &F,
        ) -> Option<Tok>
        where
            F: Fn(Vec<Tok>, S) -> Tok,
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

        let mut nesting = vec![(Vec::new(), Vec::new(), None)];
        for (indent, (mut line, line_span)) in lines {
            let mut indent = indent.as_slice();
            let mut i = 0;
            while let Some(tail) = nesting
                .get(i)
                .and_then(|(n, _, _)| indent.strip_prefix(n.as_slice()))
            {
                indent = tail;
                i += 1;
            }
            if let Some(tail) = collapse(nesting.split_off(i), &make_group) {
                nesting.last_mut().unwrap().1.push(tail);
            }
            if !indent.is_empty() {
                nesting.push((indent.to_vec(), line, Some(line_span)));
            } else {
                nesting.last_mut().unwrap().1.append(&mut line);
            }
        }

        nesting.remove(0).1
    })
}
