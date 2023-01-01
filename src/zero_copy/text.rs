use crate::{text::newline, zero_copy::prelude::*};

use super::{primitive::Any, *};

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
pub fn whitespace<'a, C: Char>(
) -> Repeated<Filter<Any<C::Slice, (), ()>, impl Fn(&C) -> bool>, C, C::Slice> {
    any().filter(|c: &C| c.is_whitespace()).repeated()
}

/// A parser that consumes text and generates tokens using semantic whitespace rules and the given token parser.
///
/// Also required is a function that collects a [`Vec`] of tokens into a whitespace-indicated token tree.
#[must_use]
pub fn semantic_indentation<'a, Tok, T, F, E: Error<str> + 'a>(
    token: T,
    make_group: F,
) -> impl Parser<'a, str, Vec<Tok>, E> + Clone + 'a
where
    Tok: Clone + 'a,
    T: Parser<'a, str, Tok, E> + Clone + 'a,
    F: Fn(Vec<Tok>, Range<usize>) -> Tok + Clone + 'a,
{
    let newline = just(char::from_ascii(b'\r'))
        .or_not()
        .ignore_then(just(char::from_ascii(b'\n')))
        .or(any().filter(|c: &char| {
            [
                '\r',       // Carriage return
                '\x0B',     // Vertical tab
                '\x0C',     // Form feed
                '\u{0085}', // Next line
                '\u{2028}', // Line separator
                '\u{2029}', // Paragraph separator
            ]
            .contains(&c.to_char())
        }));

    let line_ws = any::<str, E, _>().filter(|c: &char| c.is_inline_whitespace());

    let line = token
        .padded_by(line_ws.repeated())
        .repeated()
        .collect::<Vec<_>>()
        .padded()
        .collect::<Vec<_>>();

    let lines = line_ws
        .repeated()
        .collect::<String>()
        .then(
            line.collect::<Vec<_>>()
                .map_with_span(|line, span| (line, span)),
        )
        .separated_by(newline.padded())
        .collect::<Vec<_>>();

    lines.map(move |lines| {
        fn collapse<Tok, F>(
            mut tree: Vec<(String, Vec<Tok>, Option<Range<usize>>)>,
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

        let mut nesting = vec![(String::new(), Vec::new(), None)];
        for (mut indent, (mut line, line_span)) in lines {
            let mut indent = indent.as_str();
            let mut i = 0;
            while let Some(tail) = nesting
                .get(i)
                .and_then(|(n, _, _)| indent.strip_prefix(n.as_str()))
            {
                indent = tail;
                i += 1;
            }
            if let Some(tail) = collapse(nesting.split_off(i), &make_group) {
                nesting.last_mut().unwrap().1.push(tail);
            }
            if !indent.is_empty() {
                nesting.push((indent.to_string(), line, Some(line_span)));
            } else {
                nesting.last_mut().unwrap().1.append(&mut line);
            }
        }

        nesting.remove(0).1
    })
}
