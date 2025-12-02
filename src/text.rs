//! Text-specific parsers and utilities.
//!
//! *“Ford!" he said, "there's an infinite number of monkeys outside who want to talk to us about this script for
//! Hamlet they've worked out.”*
//!
//! The parsers in this module are generic over both Unicode ([`char`]) and ASCII ([`u8`]) characters. Most parsers take
//! a type parameter, `C`, that can be either [`u8`] or [`char`] in order to handle either case.

use crate::prelude::*;
use alloc::string::ToString;

use super::*;

/// A trait implemented by textual character types (currently, [`u8`] and [`char`]).
///
/// This trait is currently sealed to minimize the impact of breaking changes. If you find a type that you think should
/// implement this trait, please [open an issue/PR](https://github.com/zesterer/chumsky/issues/new).
pub trait Char: Copy + PartialEq + Sealed {
    /// Returns true if the character is canonically considered to be inline whitespace (i.e: not part of a newline).
    fn is_inline_whitespace(&self) -> bool;

    /// Returns true if the character is canonically considered to be whitespace.
    fn is_whitespace(&self) -> bool;

    /// Returns true if the character is canonically considered to be newline.
    fn is_newline(&self) -> bool;

    /// Return the '0' digit of the character.
    fn digit_zero() -> Self;

    /// Returns true if the character is canonically considered to be a numeric digit.
    fn is_digit(&self, radix: u32) -> bool;

    /// Returns true if the character is canonically considered to be valid for starting an identifier.
    fn is_ident_start(&self) -> bool;

    /// Returns true if the character is canonically considered to be a valid within an identifier.
    fn is_ident_continue(&self) -> bool;

    /// Returns this character as a [`char`].
    fn to_ascii(&self) -> Option<u8>;
}

impl Sealed for &Grapheme {}
impl Char for &Grapheme {
    fn is_inline_whitespace(&self) -> bool {
        self.as_str() == " " || self.as_str() == "\t"
    }

    fn is_whitespace(&self) -> bool {
        let mut iter = self.as_str().chars();
        iter.all(unicode::is_whitespace)
    }

    fn is_newline(&self) -> bool {
        [
            "\r\n",     // CR LF
            "\n",       // Newline
            "\r",       // Carriage return
            "\x0B",     // Vertical tab
            "\x0C",     // Form feed
            "\u{0085}", // Next line
            "\u{2028}", // Line separator
            "\u{2029}", // Paragraph separator
        ]
        .as_slice()
        .contains(&self.as_str())
    }

    fn digit_zero() -> Self {
        Grapheme::digit_zero()
    }

    fn is_digit(&self, radix: u32) -> bool {
        let mut iter = self.as_str().chars();
        match (iter.next(), iter.next()) {
            (Some(i), None) => i.is_digit(radix),
            _ => false,
        }
    }

    fn to_ascii(&self) -> Option<u8> {
        let mut iter = self.as_bytes().iter();
        match (iter.next(), iter.next()) {
            (Some(i), None) if i.is_ascii() => Some(*i),
            _ => None,
        }
    }

    fn is_ident_start(&self) -> bool {
        let (first, rest) = self.split();
        let is_start = unicode_ident::is_xid_start(first) || first == '_';
        is_start && rest.chars().all(unicode_ident::is_xid_continue)
    }

    fn is_ident_continue(&self) -> bool {
        let mut iter = self.as_str().chars();
        iter.all(unicode_ident::is_xid_continue)
    }
}

impl Sealed for char {}
impl Char for char {
    fn is_inline_whitespace(&self) -> bool {
        *self == ' ' || *self == '\t'
    }

    fn is_whitespace(&self) -> bool {
        unicode::is_whitespace(*self)
    }

    fn is_newline(&self) -> bool {
        [
            '\n',       // Newline
            '\r',       // Carriage return
            '\x0B',     // Vertical tab
            '\x0C',     // Form feed
            '\u{0085}', // Next line
            '\u{2028}', // Line separator
            '\u{2029}', // Paragraph separator
        ]
        .as_slice()
        .contains(self)
    }

    fn digit_zero() -> Self {
        '0'
    }

    fn is_digit(&self, radix: u32) -> bool {
        char::is_digit(*self, radix)
    }

    fn to_ascii(&self) -> Option<u8> {
        self.is_ascii().then_some(*self as u8)
    }

    fn is_ident_start(&self) -> bool {
        unicode_ident::is_xid_start(*self) || *self == '_'
    }

    fn is_ident_continue(&self) -> bool {
        unicode_ident::is_xid_continue(*self)
    }
}

impl Sealed for u8 {}
impl Char for u8 {
    fn is_inline_whitespace(&self) -> bool {
        *self == b' ' || *self == b'\t'
    }

    fn is_whitespace(&self) -> bool {
        self.is_ascii_whitespace()
    }

    fn is_newline(&self) -> bool {
        [
            b'\n',   // Newline
            b'\r',   // Carriage return
            b'\x0B', // Vertical tab
            b'\x0C', // Form feed
        ]
        .as_slice()
        .contains(self)
    }

    fn digit_zero() -> Self {
        b'0'
    }

    fn is_digit(&self, radix: u32) -> bool {
        (*self as char).is_digit(radix)
    }

    fn to_ascii(&self) -> Option<u8> {
        Some(*self)
    }

    fn is_ident_start(&self) -> bool {
        (*self as char).is_ident_start()
    }

    fn is_ident_continue(&self) -> bool {
        (*self as char).is_ident_continue()
    }
}

/// A parser that accepts (and ignores) any number of whitespace characters before or after another pattern.
#[derive(Copy, Clone)]
pub struct Padded<A> {
    pub(crate) parser: A,
}

impl<'src, I, O, E, A> Parser<'src, I, O, E> for Padded<A>
where
    I: Input<'src>,
    E: ParserExtra<'src, I>,
    I::Token: Char,
    A: Parser<'src, I, O, E>,
{
    #[doc(hidden)]
    #[cfg(feature = "debug")]
    fn node_info(&self, scope: &mut debug::NodeScope) -> debug::NodeInfo {
        debug::NodeInfo::Padded(Box::new(self.parser.node_info(scope)))
    }

    fn go<M: Mode>(&self, inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, O> {
        inp.skip_while(|c| c.is_whitespace());
        let out = self.parser.go::<M>(inp)?;
        inp.skip_while(|c| c.is_whitespace());
        Ok(out)
    }

    go_extra!(O);
}

/// Labels denoting a variety of text-related patterns.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum TextExpected<Slice> {
    /// Whitespace (for example: spaces, tabs, or newlines).
    Whitespace,
    /// Inline whitespace (for example: spaces or tabs).
    InlineWhitespace,
    /// A newline character or sequence.
    Newline,
    /// A numeric digit within the given radix range.
    ///
    /// For example:
    ///
    /// - `Digit(0, 10)` implies any base-10 digit
    /// - `Digit(1, 16)` implies any non-zero hexadecimal digit
    Digit(u32, u32),
    /// Any identifier.
    AnyIdentifier,
    /// A specific identifier.
    Identifier(Slice),
    /// An integer was expected
    Int,
}

impl<Slice: Copy> Copy for TextExpected<Slice> {}

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
/// let whitespace = text::whitespace::<_, extra::Err<Simple<char>>>();
///
/// // Any amount of whitespace is parsed...
/// assert_eq!(whitespace.parse("\t \n  \r ").into_result(), Ok(()));
/// // ...including none at all!
/// assert_eq!(whitespace.parse("").into_result(), Ok(()));
/// ```
pub fn whitespace<'src, I, E>() -> Repeated<impl Parser<'src, I, (), E> + Copy, (), I, E>
where
    I: StrInput<'src>,
    I::Token: Char + 'src,
    E: ParserExtra<'src, I>,
    E::Error: LabelError<'src, I, TextExpected<()>>,
{
    any()
        .filter(|c: &I::Token| c.is_whitespace())
        .labelled_with(|| TextExpected::Whitespace)
        .as_builtin()
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
/// let inline_whitespace = text::inline_whitespace::<_, extra::Err<Simple<char>>>();
///
/// // Any amount of inline whitespace is parsed...
/// assert_eq!(inline_whitespace.parse("\t  ").into_result(), Ok(()));
/// // ...including none at all!
/// assert_eq!(inline_whitespace.parse("").into_result(), Ok(()));
/// // ... but not newlines
/// assert!(inline_whitespace.at_least(1).parse("\n\r").has_errors());
/// ```
pub fn inline_whitespace<'src, I, E>() -> Repeated<impl Parser<'src, I, (), E> + Copy, (), I, E>
where
    I: StrInput<'src>,
    I::Token: Char + 'src,
    E: ParserExtra<'src, I>,
    E::Error: LabelError<'src, I, TextExpected<()>>,
{
    any()
        .filter(|c: &I::Token| c.is_inline_whitespace())
        .labelled_with(|| TextExpected::InlineWhitespace)
        .as_builtin()
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
pub fn newline<'src, I, E>() -> impl Parser<'src, I, (), E> + Copy
where
    I: StrInput<'src>,
    I::Token: Char + 'src,
    E: ParserExtra<'src, I>,
    &'src str: OrderedSeq<'src, I::Token>,
    E::Error: LabelError<'src, I, TextExpected<()>>,
{
    custom(|inp| {
        let before = inp.cursor();

        if inp
            .peek()
            .map_or(false, |c: I::Token| c.to_ascii() == Some(b'\r'))
        {
            inp.skip();
            if inp
                .peek()
                .map_or(false, |c: I::Token| c.to_ascii() == Some(b'\n'))
            {
                inp.skip();
            }
            Ok(())
        } else {
            let c = inp.next();
            if c.map_or(false, |c: I::Token| c.is_newline()) {
                Ok(())
            } else {
                let span = inp.span_since(&before);
                Err(LabelError::expected_found(
                    [TextExpected::Newline],
                    c.map(MaybeRef::Val),
                    span,
                ))
            }
        }
    })
    .labelled_with(|| TextExpected::Newline)
    .as_builtin()
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
/// let digits = text::digits::<_, extra::Err<Simple<char>>>(10).to_slice();
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
pub fn digits<'src, I, E>(
    radix: u32,
) -> Repeated<impl Parser<'src, I, <I as Input<'src>>::Token, E> + Copy, I::Token, I, E>
where
    I: StrInput<'src>,
    I::Token: Char + 'src,
    E: ParserExtra<'src, I>,
    E::Error: LabelError<'src, I, TextExpected<()>>,
{
    any()
        .filter(move |c: &I::Token| c.is_digit(radix))
        .labelled_with(move || TextExpected::Digit(0, radix))
        .as_builtin()
        .map_err(move |mut err: E::Error| {
            err.label_with(TextExpected::Digit(0, radix));
            err
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
/// let dec = text::int::<_, extra::Err<Simple<char>>>(10);
///
/// assert_eq!(dec.parse("0").into_result(), Ok("0"));
/// assert_eq!(dec.parse("1").into_result(), Ok("1"));
/// assert_eq!(dec.parse("1452").into_result(), Ok("1452"));
/// // No leading zeroes are permitted!
/// assert!(dec.parse("04").has_errors());
///
/// let hex = text::int::<_, extra::Err<Simple<char>>>(16);
///
/// assert_eq!(hex.parse("2A").into_result(), Ok("2A"));
/// assert_eq!(hex.parse("d").into_result(), Ok("d"));
/// assert_eq!(hex.parse("b4").into_result(), Ok("b4"));
/// assert!(hex.parse("0B").has_errors());
/// ```
///
#[must_use]
pub fn int<'src, I, E>(radix: u32) -> impl Parser<'src, I, <I as SliceInput<'src>>::Slice, E> + Copy
where
    I: StrInput<'src>,
    I::Token: Char + 'src,
    E: ParserExtra<'src, I>,
    E::Error: LabelError<'src, I, TextExpected<()>> + LabelError<'src, I, MaybeRef<'src, I::Token>>,
{
    any()
        .filter(move |c: &I::Token| c.is_digit(radix) && c != &I::Token::digit_zero())
        .then(
            any()
                .filter(move |c: &I::Token| c.is_digit(radix))
                .repeated(),
        )
        .ignored()
        .or(just(I::Token::digit_zero()).ignored())
        .to_slice()
        .labelled_with(|| TextExpected::Int)
        .as_builtin()
}

/// Parsers and utilities for working with ASCII inputs.
pub mod ascii {
    use super::*;

    /// A parser that accepts a C-style identifier.
    ///
    /// The output type of this parser is [`SliceInput::Slice`] (i.e: [`&str`] when `I` is [`&str`], and [`&[u8]`] when `I` is
    /// [`&[u8]`]).
    ///
    /// An identifier is defined as an ASCII alphabetic character or an underscore followed by any number of alphanumeric
    /// characters or underscores. The regex pattern for it is `[a-zA-Z_][a-zA-Z0-9_]*`.
    #[must_use]
    pub fn ident<'src, I, E>() -> impl Parser<'src, I, <I as SliceInput<'src>>::Slice, E> + Copy
    where
        I: StrInput<'src>,
        I::Token: Char + 'src,
        E: ParserExtra<'src, I>,
        E::Error: LabelError<'src, I, TextExpected<()>>,
    {
        any()
            .filter(|c: &I::Token| {
                c.to_ascii()
                    .map_or(false, |i| i.is_ascii_alphabetic() || i == b'_')
            })
            .then(
                any()
                    .filter(|c: &I::Token| {
                        c.to_ascii()
                            .map_or(false, |i| i.is_ascii_alphanumeric() || i == b'_')
                    })
                    .repeated(),
            )
            .to_slice()
            .labelled_with(|| TextExpected::AnyIdentifier)
            .as_builtin()
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
    /// let def = text::ascii::keyword::<_, _, extra::Err<Simple<char>>>("def");
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
    pub fn keyword<'src, I, S, E>(
        keyword: S,
    ) -> impl Parser<'src, I, <I as SliceInput<'src>>::Slice, E> + Clone + 'src
    where
        I: StrInput<'src>,
        I::Token: Char + fmt::Debug + 'src,
        S: PartialEq<I::Slice> + Clone + 'src,
        E: ParserExtra<'src, I> + 'src,
        E::Error: LabelError<'src, I, TextExpected<()>> + LabelError<'src, I, TextExpected<S>>,
    {
        /*
        #[cfg(debug_assertions)]
        {
            let mut cs = keyword.seq_iter();
            if let Some(c) = cs.next() {
                let c = c.borrow().to_char();
                assert!(c.is_ascii_alphabetic() || c == '_', "The first character of a keyword must be ASCII alphabetic or an underscore, not {:?}", c);
            } else {
                panic!("Keyword must have at least one character");
            }
            for c in cs {
                let c = c.borrow().to_char();
                assert!(c.is_ascii_alphanumeric() || c == '_', "Trailing characters of a keyword must be ASCII alphanumeric or an underscore, not {:?}", c);
            }
        }
        */
        ident()
            .try_map({
                let keyword = keyword.clone();
                move |s: I::Slice, span| {
                    if keyword == s {
                        Ok(())
                    } else {
                        Err(LabelError::expected_found(
                            [TextExpected::Identifier(keyword.clone())],
                            None,
                            span,
                        ))
                    }
                }
            })
            .to_slice()
            .labelled(TextExpected::Identifier(keyword))
            .as_builtin()
    }
}

// Unicode is the default
pub use unicode::*;

/// Parsers and utilities for working with unicode inputs.
pub mod unicode {
    use super::*;

    use core::str::{Bytes, Chars};
    use unicode_segmentation::UnicodeSegmentation;

    /// A type containing one extended Unicode grapheme cluster.
    #[derive(PartialEq, Eq)]
    #[repr(transparent)]
    pub struct Grapheme {
        inner: str,
    }

    impl Grapheme {
        fn new(inner: &str) -> &Self {
            // SAFETY: This is ok because Grapheme is #[repr(transparent)]
            unsafe { &*(inner as *const str as *const Self) }
        }

        /// Creates a new grapheme with the character `'0'` inside it.
        pub fn digit_zero() -> &'static Self {
            Self::new("0")
        }

        /// Gets an iterator over code points.
        pub fn code_points(&self) -> Chars<'_> {
            self.inner.chars()
        }

        /// Gets an iterator over bytes.
        pub fn bytes(&self) -> Bytes<'_> {
            self.inner.bytes()
        }

        /// Gets the slice of code points that are contained in the grapheme cluster.
        pub fn as_str(&self) -> &str {
            &self.inner
        }

        /// Gets the slice of bytes that are contained in the grapheme cluster.
        pub fn as_bytes(&self) -> &[u8] {
            self.inner.as_bytes()
        }

        /// Splits the grapheme into the first code point and the remaining code points.
        pub fn split(&self) -> (char, &str) {
            let mut iter = self.inner.chars();
            // The operation never falls because the grapheme always contains at least one code point.
            let first = iter.next().unwrap();
            (first, iter.as_str())
        }
    }

    impl fmt::Debug for Grapheme {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("g'")?;
            for i in self.as_str().chars() {
                write!(f, "{}", i.escape_debug())?;
            }
            f.write_str("'")?;
            Ok(())
        }
    }

    impl fmt::Display for Grapheme {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            fmt::Display::fmt(&self.inner, f)
        }
    }

    impl AsRef<str> for Grapheme {
        fn as_ref(&self) -> &str {
            self.as_str()
        }
    }

    impl AsRef<[u8]> for Grapheme {
        fn as_ref(&self) -> &[u8] {
            self.as_bytes()
        }
    }

    impl AsRef<Grapheme> for Grapheme {
        fn as_ref(&self) -> &Grapheme {
            self
        }
    }

    impl Borrow<str> for Grapheme {
        fn borrow(&self) -> &str {
            self.as_str()
        }
    }

    impl Borrow<[u8]> for Grapheme {
        fn borrow(&self) -> &[u8] {
            self.as_bytes()
        }
    }

    impl<'src> From<&'src Grapheme> for Box<Grapheme> {
        fn from(value: &'src Grapheme) -> Self {
            let value: Box<str> = Box::from(value.as_str());
            // SAFETY: This is ok because Grapheme is #[repr(transparent)]
            unsafe { Box::from_raw(Box::into_raw(value) as *mut Grapheme) }
        }
    }

    impl From<Box<Grapheme>> for Box<str> {
        fn from(value: Box<Grapheme>) -> Self {
            // SAFETY: This is ok because Grapheme is #[repr(transparent)]
            unsafe { Box::from_raw(Box::into_raw(value) as *mut str) }
        }
    }

    impl From<Box<Grapheme>> for Box<[u8]> {
        fn from(value: Box<Grapheme>) -> Self {
            Box::<str>::from(value).into()
        }
    }

    /// A type containing any number of extended Unicode grapheme clusters.
    #[derive(PartialEq, Eq)]
    #[repr(transparent)]
    pub struct Graphemes {
        inner: str,
    }

    impl Graphemes {
        /// Create a new graphemes.
        pub fn new(inner: &str) -> &Self {
            // SAFETY: This is ok because Graphemes is #[repr(transparent)]
            unsafe { &*(inner as *const str as *const Self) }
        }

        /// Gets an iterator over graphemes.
        pub fn iter(&self) -> GraphemesIter<'_> {
            self.into_iter()
        }

        /// Gets an iterator over code points.
        pub fn code_points(&self) -> Chars<'_> {
            self.inner.chars()
        }

        /// Gets an iterator over bytes.
        pub fn bytes(&self) -> Bytes<'_> {
            self.inner.bytes()
        }

        /// Gets the slice of code points that are contained in the string.
        pub fn as_str(&self) -> &str {
            &self.inner
        }

        /// Gets the slice of bytes that are contained in the string.
        pub fn as_bytes(&self) -> &[u8] {
            self.inner.as_bytes()
        }
    }

    impl fmt::Debug for Graphemes {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("g")?;
            fmt::Debug::fmt(&self.inner, f)
        }
    }

    impl fmt::Display for Graphemes {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            fmt::Display::fmt(&self.inner, f)
        }
    }

    impl AsRef<str> for Graphemes {
        fn as_ref(&self) -> &str {
            self.as_str()
        }
    }

    impl AsRef<[u8]> for Graphemes {
        fn as_ref(&self) -> &[u8] {
            self.as_bytes()
        }
    }

    impl AsRef<Graphemes> for Graphemes {
        fn as_ref(&self) -> &Graphemes {
            self
        }
    }

    impl Borrow<str> for Graphemes {
        fn borrow(&self) -> &str {
            self.as_str()
        }
    }

    impl Borrow<[u8]> for Graphemes {
        fn borrow(&self) -> &[u8] {
            self.as_bytes()
        }
    }

    impl<'src> From<&'src str> for &'src Graphemes {
        fn from(value: &'src str) -> Self {
            Graphemes::new(value)
        }
    }

    impl<'src> From<&'src Graphemes> for &'src str {
        fn from(value: &'src Graphemes) -> Self {
            value.as_str()
        }
    }

    impl<'src> From<&'src Graphemes> for Box<Graphemes> {
        fn from(value: &'src Graphemes) -> Self {
            value.as_str().into()
        }
    }

    impl<'src> From<&'src str> for Box<Graphemes> {
        fn from(value: &'src str) -> Self {
            Box::<str>::from(value).into()
        }
    }

    impl From<Box<str>> for Box<Graphemes> {
        fn from(value: Box<str>) -> Self {
            // SAFETY: This is ok because Grapheme is #[repr(transparent)]
            unsafe { Box::from_raw(Box::into_raw(value) as *mut Graphemes) }
        }
    }

    impl From<Box<Graphemes>> for Box<str> {
        fn from(value: Box<Graphemes>) -> Self {
            // SAFETY: This is ok because Grapheme is #[repr(transparent)]
            unsafe { Box::from_raw(Box::into_raw(value) as *mut str) }
        }
    }

    impl From<Box<Graphemes>> for Box<[u8]> {
        fn from(value: Box<Graphemes>) -> Self {
            Box::<str>::from(value).into()
        }
    }

    impl<'src> IntoIterator for &'src Graphemes {
        type Item = &'src Grapheme;

        type IntoIter = GraphemesIter<'src>;

        fn into_iter(self) -> Self::IntoIter {
            GraphemesIter::new(self)
        }
    }

    impl Sealed for &'_ Graphemes {}
    impl<'src> StrInput<'src> for &'src Graphemes {
        #[doc(hidden)]
        fn stringify(slice: Self::Slice) -> String {
            slice.to_string()
        }
    }

    impl<'src> Input<'src> for &'src Graphemes {
        type Cursor = usize;
        type Span = SimpleSpan<usize>;

        type Token = &'src Grapheme;
        type MaybeToken = &'src Grapheme;

        type Cache = Self;

        #[inline]
        fn begin(self) -> (Self::Cursor, Self::Cache) {
            (0, self)
        }

        #[inline]
        fn cursor_location(cursor: &Self::Cursor) -> usize {
            *cursor
        }

        #[inline(always)]
        unsafe fn next_maybe(
            this: &mut Self::Cache,
            cursor: &mut Self::Cursor,
        ) -> Option<Self::MaybeToken> {
            if *cursor < this.as_str().len() {
                // SAFETY: `cursor < self.len()` above guarantees cursor is in-bounds
                //         We only ever return cursors that are at a code point boundary.
                //         The `next()` implementation returns `None`, only in the
                //         situation of zero length of the remaining part of the string.
                //         And the Unicode standard guarantees that any sequence of code
                //         points is a valid sequence of grapheme clusters, so the
                //         behaviour of the `next()` function should not change.
                let c = this
                    .as_str()
                    .get_unchecked(*cursor..)
                    .graphemes(true)
                    .next()
                    .unwrap_unchecked();
                *cursor += c.len();
                Some(Grapheme::new(c))
            } else {
                None
            }
        }

        #[inline(always)]
        unsafe fn span(_this: &mut Self::Cache, range: Range<&Self::Cursor>) -> Self::Span {
            (*range.start..*range.end).into()
        }
    }

    impl<'src> ExactSizeInput<'src> for &'src Graphemes {
        #[inline(always)]
        unsafe fn span_from(this: &mut Self::Cache, range: RangeFrom<&Self::Cursor>) -> Self::Span {
            (*range.start..this.as_str().len()).into()
        }
    }

    impl<'src> ValueInput<'src> for &'src Graphemes {
        #[inline(always)]
        unsafe fn next(this: &mut Self::Cache, cursor: &mut Self::Cursor) -> Option<Self::Token> {
            Self::next_maybe(this, cursor)
        }
    }

    impl<'src> SliceInput<'src> for &'src Graphemes {
        type Slice = Self;

        #[inline(always)]
        fn full_slice(this: &mut Self::Cache) -> Self::Slice {
            *this
        }

        #[inline(always)]
        unsafe fn slice(this: &mut Self::Cache, range: Range<&Self::Cursor>) -> Self::Slice {
            Graphemes::new(&this.as_str()[*range.start..*range.end])
        }

        #[inline(always)]
        unsafe fn slice_from(
            this: &mut Self::Cache,
            from: RangeFrom<&Self::Cursor>,
        ) -> Self::Slice {
            Graphemes::new(&this.as_str()[*from.start..])
        }
    }

    /// Grapheme iterator type.
    #[derive(Debug, Clone)]
    pub struct GraphemesIter<'src> {
        iter: unicode_segmentation::Graphemes<'src>,
    }

    impl<'src> GraphemesIter<'src> {
        /// Create a new grapheme iterator.
        pub fn new(graphemes: &'src Graphemes) -> Self {
            Self {
                iter: graphemes.as_str().graphemes(true),
            }
        }

        /// Gets the slice of code points that are contained in the grapheme cluster.
        pub fn as_str(self) -> &'src str {
            self.iter.as_str()
        }
    }

    impl<'src> Iterator for GraphemesIter<'src> {
        type Item = &'src Grapheme;

        #[inline]
        fn size_hint(&self) -> (usize, Option<usize>) {
            self.iter.size_hint()
        }

        #[inline]
        fn next(&mut self) -> Option<Self::Item> {
            self.iter.next().map(Grapheme::new)
        }
    }

    impl DoubleEndedIterator for GraphemesIter<'_> {
        #[inline]
        fn next_back(&mut self) -> Option<Self::Item> {
            self.iter.next_back().map(Grapheme::new)
        }
    }

    /// A parser that accepts an identifier.
    ///
    /// The output type of this parser is [`SliceInput::Slice`] (i.e: [`&str`] when `I` is [`&str`], and [`&[u8]`] when `I` is
    /// [`&[u8]`]).
    ///
    /// An identifier is defined as per "Default Identifiers" in [Unicode Standard Annex #31](https://www.unicode.org/reports/tr31/).
    #[must_use]
    pub fn ident<'src, I, E>() -> impl Parser<'src, I, <I as SliceInput<'src>>::Slice, E> + Copy
    where
        I: StrInput<'src>,
        I::Token: Char + 'src,
        E: ParserExtra<'src, I>,
        E::Error: LabelError<'src, I, TextExpected<()>>,
    {
        any()
            .filter(|c: &I::Token| c.is_ident_start())
            .then(
                any()
                    .filter(|c: &I::Token| c.is_ident_continue())
                    .repeated(),
            )
            .to_slice()
            .labelled(TextExpected::AnyIdentifier)
            .as_builtin()
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
    /// let def = text::ascii::keyword::<_, _, extra::Err<Simple<char>>>("def");
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
    pub fn keyword<'src, I, S, E>(
        keyword: S,
    ) -> impl Parser<'src, I, <I as SliceInput<'src>>::Slice, E> + Clone + 'src
    where
        I: StrInput<'src>,
        I::Slice: PartialEq,
        I::Token: Char + fmt::Debug + 'src,
        S: PartialEq<I::Slice> + Clone + 'src,
        E: ParserExtra<'src, I> + 'src,
        E::Error: LabelError<'src, I, TextExpected<()>> + LabelError<'src, I, TextExpected<S>>,
    {
        /*
        #[cfg(debug_assertions)]
        {
            let mut cs = keyword.seq_iter();
            if let Some(c) = cs.next() {
                let c = c.borrow();
                assert!(
                    c.is_ident_start(),
                    "The first character of a keyword must be a valid unicode XID_START, not {:?}",
                    c
                );
            } else {
                panic!("Keyword must have at least one character");
            }
            for c in cs {
                let c = c.borrow();
                assert!(c.is_ident_continue(), "Trailing characters of a keyword must be valid as unicode XID_CONTINUE, not {:?}", c);
            }
        }
        */
        ident()
            .try_map({
                let keyword = keyword.clone();
                move |s: I::Slice, span| {
                    if keyword == s {
                        Ok(())
                    } else {
                        Err(LabelError::expected_found(
                            [TextExpected::Identifier(keyword.clone())],
                            None,
                            span,
                        ))
                    }
                }
            })
            .to_slice()
            .labelled(TextExpected::Identifier(keyword.clone()))
            .as_builtin()
    }

    /// Like [`char::is_whitespace`], but rejects the characters U+202A, U+202B, U+202C, U+202D, U+202E, U+2066, U+2067, U+2068, U+2069
    /// to mitigate against [CVE-2021-42574](https://nvd.nist.gov/vuln/detail/CVE-2021-42574)
    pub fn is_whitespace(c: char) -> bool {
        c.is_whitespace()
            && !matches!(
                c,
                '\u{202A}'
                    | '\u{202B}'
                    | '\u{202C}'
                    | '\u{202D}'
                    | '\u{202E}'
                    | '\u{2066}'
                    | '\u{2067}'
                    | '\u{2068}'
                    | '\u{2069}'
            )
    }
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;
    use std::fmt;

    fn make_ascii_kw_parser<'src, I>(s: I::Slice) -> impl Parser<'src, I, ()>
    where
        I: crate::StrInput<'src>,
        I::Slice: PartialEq,
        I::Token: crate::Char + fmt::Debug + 'src,
    {
        text::ascii::keyword(s).ignored()
    }

    fn make_unicode_kw_parser<'src, I>(s: I::Slice) -> impl Parser<'src, I, ()>
    where
        I: crate::StrInput<'src>,
        I::Slice: PartialEq,
        I::Token: crate::Char + fmt::Debug + 'src,
    {
        text::unicode::keyword(s).ignored()
    }

    fn test_ok<'src, P: Parser<'src, &'src str, &'src str>>(parser: P, input: &'src str) {
        assert_eq!(
            parser.parse(input),
            ParseResult {
                output: Some(input),
                errs: vec![]
            }
        );
    }

    fn test_err<'src, P: Parser<'src, &'src str, &'src str>>(parser: P, input: &'src str) {
        assert_eq!(
            parser.parse(input),
            ParseResult {
                output: None,
                errs: vec![EmptyErr::default()]
            }
        );
    }

    #[test]
    fn keyword_good() {
        make_ascii_kw_parser::<&str>("hello");
        make_ascii_kw_parser::<&str>("_42");
        make_ascii_kw_parser::<&str>("_42");

        make_unicode_kw_parser::<&str>("שלום");
        make_unicode_kw_parser::<&str>("привет");
        make_unicode_kw_parser::<&str>("你好");
    }

    #[test]
    fn ident() {
        let ident = text::ident::<&str, extra::Default>();
        test_ok(ident, "foo");
        test_ok(ident, "foo_bar");
        test_ok(ident, "foo_");
        test_ok(ident, "_foo");
        test_ok(ident, "_");
        test_ok(ident, "__");
        test_ok(ident, "__init__");
        test_err(ident, "");
        test_err(ident, ".");
        test_err(ident, "123");
    }

    #[test]
    fn whitespace() {
        use crate::{whitespace, LabelError, TextExpected};

        let parser = whitespace::<&str, extra::Err<Rich<_>>>().exactly(1);

        assert_eq!(
            parser.parse("").into_output_errors(),
            (
                None,
                vec![LabelError::<&str, _>::expected_found(
                    vec![TextExpected::<&str>::Whitespace],
                    None,
                    SimpleSpan::new((), 0..0)
                )]
            )
        );
    }

    /*
    #[test]
    #[should_panic]
    fn keyword_numeric() {
        make_ascii_kw_parser::<&str>("42");
    }

    #[test]
    #[should_panic]
    fn keyword_empty() {
        make_ascii_kw_parser::<&str>("");
    }

    #[test]
    #[should_panic]
    fn keyword_not_alphanum() {
        make_ascii_kw_parser::<&str>("hi\n");
    }

    #[test]
    #[should_panic]
    fn keyword_unicode_in_ascii() {
        make_ascii_kw_parser::<&str>("שלום");
    }
    */
}
