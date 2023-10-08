//! Text-specific parsers and utilities.
//!
//! *“Ford!" he said, "there's an infinite number of monkeys outside who want to talk to us about this script for
//! Hamlet they've worked out.”*
//!
//! The parsers in this module are generic over both Unicode ([`char`]) and ASCII ([`u8`]) characters. Most parsers take
//! a type parameter, `C`, that can be either [`u8`] or [`char`] in order to handle either case.

use crate::prelude::*;

use super::*;

/// A trait implemented by textual character types (currently, [`u8`] and [`char`]).
///
/// This trait is currently sealed to minimize the impact of breaking changes. If you find a type that you think should
/// implement this trait, please [open an issue/PR](https://github.com/zesterer/chumsky/issues/new).
pub trait Char: Sized + Copy + PartialEq + fmt::Debug + Sealed + 'static {
    /// The default unsized [`str`]-like type of a linear sequence of this character.
    ///
    /// For [`char`], this is [`str`]. For [`u8`], this is [`[u8]`].
    type Str: ?Sized + AsRef<[u8]> + AsRef<Self::Str> + 'static;

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

    /// Returns true if the character is canonically considered to be valid for starting an identifier.
    fn is_ident_start(&self) -> bool;

    /// Returns true if the character is canonically considered to be a valid within an identifier.
    fn is_ident_continue(&self) -> bool;

    /// Returns this character as a [`char`].
    fn to_char(&self) -> char;

    /// The iterator returned by `Self::str_to_chars`.
    type StrCharIter<'a>: Iterator<Item = Self>;

    /// Turn a string of this character type into an iterator over those characters.
    fn str_to_chars(s: &Self::Str) -> Self::StrCharIter<'_>;
}

impl Sealed for char {}
impl Char for char {
    type Str = str;

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

    type StrCharIter<'a> = core::str::Chars<'a>;
    fn str_to_chars(s: &Self::Str) -> Self::StrCharIter<'_> {
        s.chars()
    }

    fn is_ident_start(&self) -> bool {
        unicode_ident::is_xid_start(*self)
    }

    fn is_ident_continue(&self) -> bool {
        unicode_ident::is_xid_continue(*self)
    }
}

impl Sealed for u8 {}
impl Char for u8 {
    type Str = [u8];

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

    type StrCharIter<'a> = core::iter::Copied<core::slice::Iter<'a, u8>>;
    fn str_to_chars(s: &Self::Str) -> Self::StrCharIter<'_> {
        s.iter().copied()
    }

    fn is_ident_start(&self) -> bool {
        self.to_char().is_ident_start()
    }

    fn is_ident_continue(&self) -> bool {
        self.to_char().is_ident_continue()
    }
}

/// A parser that accepts (and ignores) any number of whitespace characters before or after another pattern.
#[derive(Copy, Clone)]
pub struct Padded<A> {
    pub(crate) parser: A,
}

impl<'a, I, O, E, A> ParserSealed<'a, I, O, E> for Padded<A>
where
    I: ValueInput<'a>,
    E: ParserExtra<'a, I>,
    I::Token: Char,
    A: Parser<'a, I, O, E>,
{
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
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
/// # use chumsky::prelude::*;
/// let whitespace = text::whitespace::<_, _, extra::Err<Simple<char>>>();
///
/// // Any amount of whitespace is parsed...
/// assert_eq!(whitespace.parse("\t \n  \r ").into_result(), Ok(()));
/// // ...including none at all!
/// assert_eq!(whitespace.parse("").into_result(), Ok(()));
/// ```
pub fn whitespace<'a, C: Char, I: ValueInput<'a> + StrInput<'a, C>, E: ParserExtra<'a, I>>(
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
/// # use chumsky::prelude::*;
/// let inline_whitespace = text::inline_whitespace::<_, _, extra::Err<Simple<char>>>();
///
/// // Any amount of inline whitespace is parsed...
/// assert_eq!(inline_whitespace.parse("\t  ").into_result(), Ok(()));
/// // ...including none at all!
/// assert_eq!(inline_whitespace.parse("").into_result(), Ok(()));
/// // ... but not newlines
/// assert!(inline_whitespace.at_least(1).parse("\n\r").has_errors());
/// ```
pub fn inline_whitespace<'a, C: Char, I: ValueInput<'a> + StrInput<'a, C>, E: ParserExtra<'a, I>>(
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
/// This parser is quite extensive, recognizing:
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
/// let newline = text::newline::<_, extra::Err<Simple<char>>>();
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
pub fn newline<'a, I: ValueInput<'a>, E: ParserExtra<'a, I>>(
) -> impl Parser<'a, I, (), E> + Copy + Clone
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
/// # use chumsky::prelude::*;
/// let digits = text::digits::<_, _, extra::Err<Simple<char>>>(10).to_slice();
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
    I: ValueInput<'a> + Input<'a, Token = C>,
    E: ParserExtra<'a, I>,
{
    any()
        // Use try_map over filter to get a better error on failure
        .try_map(move |c: C, span| {
            if c.is_digit(radix) {
                Ok(c)
            } else {
                Err(Error::expected_found([], Some(MaybeRef::Val(c)), span))
            }
        })
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
/// # use chumsky::prelude::*;
/// let dec = text::int::<_, _, extra::Err<Simple<char>>>(10);
///
/// assert_eq!(dec.parse("0").into_result(), Ok("0"));
/// assert_eq!(dec.parse("1").into_result(), Ok("1"));
/// assert_eq!(dec.parse("1452").into_result(), Ok("1452"));
/// // No leading zeroes are permitted!
/// assert!(dec.parse("04").has_errors());
///
/// let hex = text::int::<_, _, extra::Err<Simple<char>>>(16);
///
/// assert_eq!(hex.parse("2A").into_result(), Ok("2A"));
/// assert_eq!(hex.parse("d").into_result(), Ok("d"));
/// assert_eq!(hex.parse("b4").into_result(), Ok("b4"));
/// assert!(hex.parse("0B").has_errors());
/// ```
///
#[must_use]
pub fn int<'a, I: ValueInput<'a> + StrInput<'a, C>, C: Char, E: ParserExtra<'a, I>>(
    radix: u32,
) -> impl Parser<'a, I, &'a C::Str, E> + Copy + Clone {
    any()
        // Use try_map over filter to get a better error on failure
        .try_map(move |c: C, span| {
            if c.is_digit(radix) && c != C::digit_zero() {
                Ok(c)
            } else {
                Err(Error::expected_found([], Some(MaybeRef::Val(c)), span))
            }
        })
        // This error never appears due to `repeated` so can use `filter`
        .then(any().filter(move |c: &C| c.is_digit(radix)).repeated())
        .ignored()
        .or(just(C::digit_zero()).ignored())
        .to_slice()
}

/// Parsers and utilities for working with ASCII inputs.
pub mod ascii {
    use super::*;

    /// A parser that accepts a C-style identifier.
    ///
    /// The output type of this parser is [`Char::Str`] (i.e: [`&str`] when `C` is [`char`], and [`&[u8]`] when `C` is
    /// [`u8`]).
    ///
    /// An identifier is defined as an ASCII alphabetic character or an underscore followed by any number of alphanumeric
    /// characters or underscores. The regex pattern for it is `[a-zA-Z_][a-zA-Z0-9_]*`.
    #[must_use]
    pub fn ident<'a, I: ValueInput<'a> + StrInput<'a, C>, C: Char, E: ParserExtra<'a, I>>(
    ) -> impl Parser<'a, I, &'a C::Str, E> + Copy + Clone {
        any()
            // Use try_map over filter to get a better error on failure
            .try_map(|c: C, span| {
                if c.to_char().is_ascii_alphabetic() || c.to_char() == '_' {
                    Ok(c)
                } else {
                    Err(Error::expected_found([], Some(MaybeRef::Val(c)), span))
                }
            })
            .then(
                any()
                    // This error never appears due to `repeated` so can use `filter`
                    .filter(|c: &C| c.to_char().is_ascii_alphanumeric() || c.to_char() == '_')
                    .repeated(),
            )
            .to_slice()
    }

    /// Like [`ident`], but only accepts a specific identifier while rejecting trailing identifier characters.
    ///
    /// The output type of this parser is `I::Slice` (i.e: [`&str`] when `I` is [`&str`], and [`&[u8]`]
    /// when `I::Slice` is [`&[u8]`]).
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// let def = text::ascii::keyword::<_, _, _, extra::Err<Simple<char>>>("def");
    ///
    /// // Exactly 'def' was found
    /// assert_eq!(def.parse("def").into_result(), Ok("def"));
    /// // Exactly 'def' was found, with non-identifier trailing characters
    /// // This works because we made the parser lazy: it parses 'def' and ignores the rest
    /// assert_eq!(def.clone().lazy().parse("def(foo, bar)").into_result(), Ok("def"));
    /// // 'def' was found, but only as part of a larger identifier, so this fails to parse
    /// assert!(def.lazy().parse("define").has_errors());
    /// ```
    #[track_caller]
    pub fn keyword<
        'a,
        I: ValueInput<'a> + StrInput<'a, C>,
        C: Char + 'a,
        Str: AsRef<C::Str> + 'a + Clone,
        E: ParserExtra<'a, I> + 'a,
    >(
        keyword: Str,
    ) -> impl Parser<'a, I, &'a C::Str, E> + Clone + 'a
    where
        C::Str: PartialEq,
    {
        #[cfg(debug_assertions)]
        {
            let mut cs = C::str_to_chars(keyword.as_ref());
            if let Some(c) = cs.next() {
                assert!(c.to_char().is_ascii_alphabetic() || c.to_char() == '_', "The first character of a keyword must be ASCII alphabetic or an underscore, not {:?}", c);
            } else {
                panic!("Keyword must have at least one character");
            }
            for c in cs {
                assert!(c.to_char().is_ascii_alphanumeric() || c.to_char() == '_', "Trailing characters of a keyword must be ASCII alphanumeric or an underscore, not {:?}", c);
            }
        }
        ident()
            .try_map(move |s: &C::Str, span| {
                if s == keyword.as_ref() {
                    Ok(())
                } else {
                    Err(Error::expected_found(None, None, span))
                }
            })
            .to_slice()
    }
}

// Unicode is the default
pub use unicode::*;

/// Parsers and utilities for working with unicode inputs.
pub mod unicode {
    use super::*;

    /// A parser that accepts an identifier.
    ///
    /// The output type of this parser is [`Char::Str`] (i.e: [`&str`] when `C` is [`char`], and [`&[u8]`] when `C` is
    /// [`u8`]).
    ///
    /// An identifier is defined as per "Default Identifiers" in [Unicode Standard Annex #31](https://www.unicode.org/reports/tr31/).
    #[must_use]
    pub fn ident<'a, I: ValueInput<'a> + StrInput<'a, C>, C: Char, E: ParserExtra<'a, I>>(
    ) -> impl Parser<'a, I, &'a C::Str, E> + Copy + Clone {
        any()
            // Use try_map over filter to get a better error on failure
            .try_map(|c: C, span| {
                if c.is_ident_start() {
                    Ok(c)
                } else {
                    Err(Error::expected_found([], Some(MaybeRef::Val(c)), span))
                }
            })
            .then(
                any()
                    // This error never appears due to `repeated` so can use `filter`
                    .filter(|c: &C| c.is_ident_continue())
                    .repeated(),
            )
            .to_slice()
    }

    /// Like [`ident`], but only accepts a specific identifier while rejecting trailing identifier characters.
    ///
    /// The output type of this parser is `I::Slice` (i.e: [`&str`] when `I` is [`&str`], and [`&[u8]`]
    /// when `I::Slice` is [`&[u8]`]).
    ///
    /// # Examples
    ///
    /// ```
    /// # use chumsky::prelude::*;
    /// let def = text::ascii::keyword::<_, _, _, extra::Err<Simple<char>>>("def");
    ///
    /// // Exactly 'def' was found
    /// assert_eq!(def.parse("def").into_result(), Ok("def"));
    /// // Exactly 'def' was found, with non-identifier trailing characters
    /// // This works because we made the parser lazy: it parses 'def' and ignores the rest
    /// assert_eq!(def.clone().lazy().parse("def(foo, bar)").into_result(), Ok("def"));
    /// // 'def' was found, but only as part of a larger identifier, so this fails to parse
    /// assert!(def.lazy().parse("define").has_errors());
    /// ```
    #[track_caller]
    pub fn keyword<
        'a,
        I: ValueInput<'a> + StrInput<'a, C>,
        C: Char + 'a,
        Str: AsRef<C::Str> + 'a + Clone,
        E: ParserExtra<'a, I> + 'a,
    >(
        keyword: Str,
    ) -> impl Parser<'a, I, &'a C::Str, E> + Clone + 'a
    where
        C::Str: PartialEq,
    {
        #[cfg(debug_assertions)]
        {
            let mut cs = C::str_to_chars(keyword.as_ref());
            if let Some(c) = cs.next() {
                assert!(
                    c.is_ident_start(),
                    "The first character of a keyword must be a valid unicode XID_START, not {:?}",
                    c
                );
            } else {
                panic!("Keyword must have at least one character");
            }
            for c in cs {
                assert!(c.is_ident_continue(), "Trailing characters of a keyword must be valid as unicode XID_CONTINUE, not {:?}", c);
            }
        }
        ident()
            .try_map(move |s: &C::Str, span| {
                if s == keyword.as_ref() {
                    Ok(())
                } else {
                    Err(Error::expected_found(None, None, span))
                }
            })
            .to_slice()
    }
}

// TODO: Better native form of semantic indentation that uses the context system?

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    fn make_ascii_kw_parser<'a, C: text::Char, I: crate::StrInput<'a, C>>(
        s: &'a C::Str,
    ) -> impl Parser<'a, I, ()>
    where
        C::Str: PartialEq,
    {
        text::ascii::keyword(s).ignored()
    }

    fn make_unicode_kw_parser<'a, C: text::Char, I: crate::StrInput<'a, C>>(
        s: &'a C::Str,
    ) -> impl Parser<'a, I, ()>
    where
        C::Str: PartialEq,
    {
        text::unicode::keyword(s).ignored()
    }

    #[test]
    fn keyword_good() {
        make_ascii_kw_parser::<char, &str>("hello");
        make_ascii_kw_parser::<char, &str>("_42");

        make_unicode_kw_parser::<char, &str>("שלום");
        make_unicode_kw_parser::<char, &str>("привет");
        make_unicode_kw_parser::<char, &str>("你好");
    }

    #[test]
    #[should_panic]
    fn keyword_numeric() {
        make_ascii_kw_parser::<char, &str>("42");
    }

    #[test]
    #[should_panic]
    fn keyword_empty() {
        make_ascii_kw_parser::<char, &str>("");
    }

    #[test]
    #[should_panic]
    fn keyword_not_alphanum() {
        make_ascii_kw_parser::<char, &str>("hi\n");
    }

    #[test]
    #[should_panic]
    fn keyword_unicode_in_ascii() {
        make_ascii_kw_parser::<char, &str>("שלום");
    }
}
