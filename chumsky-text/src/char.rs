/// A trait implemented by textual character types (currently, [`u8`] and [`char`]).
///
/// This trait is currently sealed to minimise the impact of breaking changes. If you find a type that you think should
/// implement this trait, please [open an issue/PR](https://github.com/zesterer/chumsky/issues/new).
pub trait Char: Sized + Copy + PartialEq + std::fmt::Debug + 'static {
    /// The default unsized [`str`]-like type of a linear sequence of this character.
    ///
    /// For [`char`], this is [`str`]. For [`u8`], this is [`[u8]`].
    type Str: ?Sized + AsRef<Self::Str> + 'static;

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
