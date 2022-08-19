use super::*;

pub trait Char: Sized {
    type Slice: ?Sized + StrInput<Self> + 'static;

    #[cfg(feature = "regex")]
    type Regex;

    #[cfg(feature = "regex")]
    #[doc(hidden)]
    fn new_regex(pattern: &str) -> Self::Regex;
    #[cfg(feature = "regex")]
    #[doc(hidden)]
    fn match_regex(regex: &Self::Regex, trailing: &Self::Slice) -> Option<usize>;

    fn is_whitespace(&self) -> bool;

    fn is_digit(&self, radix: u32) -> bool;

    fn is_zero(&self) -> bool;
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

    fn is_whitespace(&self) -> bool {
        (*self).is_whitespace()
    }

    fn is_digit(&self, radix: u32) -> bool {
        char::is_digit(*self, radix)
    }

    fn is_zero(&self) -> bool {
        *self == '0'
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

    fn is_whitespace(&self) -> bool {
        self.is_ascii_whitespace()
    }

    fn is_digit(&self, radix: u32) -> bool {
        char::from(*self).is_digit(radix)
    }

    fn is_zero(&self) -> bool {
        *self == b'0'
    }
}

#[derive(Clone)]
pub struct Padded<A> {
    pub(crate) parser: A,
}

impl<'a, I, E, S, A> Parser<'a, I, E, S> for Padded<A>
where
    I: Input + ?Sized,
    E: Error<I>,
    S: 'a,
    I::Token: Char,
    A: Parser<'a, I, E, S>,
{
    type Output = A::Output;

    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E, S>) -> PResult<M, Self::Output, E> {
        inp.skip_while(|c| c.is_whitespace());
        let out = self.parser.go::<M>(inp)?;
        inp.skip_while(|c| c.is_whitespace());
        Ok(out)
    }

    go_extra!();
}

/// A parser that accepts (and ignores) any number of whitespace characters.
///
/// The output type of this parser is `()`.
#[must_use]
pub fn whitespace<I, E, S>() -> impl for<'a> Parser<'a, I, E, S, Output = ()>
where
    I: SliceInput + ?Sized,
    I::Token: Char,
    E: Error<I>,
    for<'a> S: 'a,
{
    primitive::any()
        .filter(|x: &I::Token| x.is_whitespace())
        .repeated()
        .ignored()
}

/// A parser that accepts one or more ASCII digits.
///
/// The `radix` parameter functions identically to [`char::is_digit`]. If in doubt, choose `10`.
#[must_use]
pub fn digits<'a, I, E, S, C>(
    radix: u32,
) -> Map<
    RepeatedSlice<impl Parser<'a, I, E, S, Output = I::Token>, I, E, S>,
    fn(&'a <I as SliceInput>::Slice) -> C,
>
where
    I: SliceInput + ?Sized,
    I::Token: Char,
    <I as SliceInput>::Slice: 'a,
    E: Error<I>,
    S: 'a,
    C: From<&'a <I as SliceInput>::Slice>,
{
    primitive::any()
        .filter(move |x: &I::Token| x.is_digit(radix))
        .repeated_slice()
        .at_least(1)
        .map(C::from)
}

/// A parser that accepts a non-negative integer.
///
/// An integer is defined as a non-empty sequence of ASCII digits, where the first digit is non-zero or the sequence
/// has length one.
///
/// The `radix` parameter functions identically to [`char::is_digit`]. If in doubt, choose `10`.
#[must_use]
pub fn int<'a, I, E, S, C>(radix: u32) -> impl Parser<'a, I, E, S, Output = C>
where
    I: SliceInput + ?Sized,
    I::Token: Char,
    <I as SliceInput>::Slice: 'a,
    E: Error<I>,
    S: 'a,
    C: From<&'a <I as SliceInput>::Slice>,
{
    primitive::any()
        .filter(move |x: &I::Token| x.is_zero())
        .repeated_slice()
        .exactly(1)
        .or(primitive::any()
            .filter(move |x: &I::Token| x.is_digit(radix))
            .repeated_slice()
            .at_least(1))
        .map(C::from)
}

#[cfg(test)]
mod tests {
    use super::*;

    mod whitespace {
        use super::*;

        #[test]
        fn parses_whitespace() {
            let res = whitespace::<_, (), ()>().parse(" \x09\x0A\x0B\x0C\x0D");
            assert_eq!(res, (Some(()), Vec::new()));
        }

        #[test]
        fn parses_whitespace_stops_on_non() {
            let res = whitespace::<_, (), ()>().parse("\x09\x0A f \x0B\x0C\x0D");
            assert_eq!(res, (Some(()), Vec::new()));
        }

        #[test]
        fn parse_whitespace_independent_from_lifetime() {
            let res = {
                let a = String::from("       ");
                whitespace::<_, (), ()>().parse(&*a)
            };

            assert_eq!(res, (Some(()), Vec::new()));
        }

        #[test]
        fn parses_whitespace_bytes() {
            // '\x0B' is classified as unicode whitespace, but not ascii-whitespace,
            // so it is NOT counted as whitespace for this test
            let res = whitespace::<_, (), ()>().parse(" \x09\x0A\x0B\x0C\x0D".as_bytes());
            assert_eq!(res, (Some(()), Vec::new()));

            let res = whitespace::<_, (), ()>().parse("\x0C\x0D".as_bytes());
            assert_eq!(res, (Some(()), Vec::new()));
        }

        #[test]
        fn parses_whitespace_bytes_stops_at_non() {
            let res = whitespace::<_, (), ()>().parse(b"\x09\x0Af\x0B\x0C\x0D".as_slice());
            assert_eq!(res, (Some(()), Vec::new()));

            // '\x0B' is classified as unicode whitespace, but not ascii-whitespace,
            // so it is NOT counted as whitespace for this test
            let res = whitespace::<_, (), ()>().parse(b"\x0B\x0C\x0D".as_slice());
            assert_eq!(res, (Some(()), Vec::new()));

            let res = whitespace::<_, (), ()>().parse(b"\x0C\x0D".as_slice());
            assert_eq!(res, (Some(()), Vec::new()));
        }

        #[test]
        fn parses_whitespace_bytes_independent_from_lifetime() {
            let res = {
                let a = String::from("       ");
                whitespace::<_, (), ()>().parse(a.as_bytes())
            };

            assert_eq!(res, (Some(()), Vec::new()));
        }
    }

    mod numbers {
        use super::*;

        #[test]
        fn parses_digits() {
            let res = digits::<_, (), (), _>(10).parse("0123456789");
            assert_eq!(res, (Some("0123456789".to_string()), Vec::new()));
        }

        #[test]
        fn parses_digits_into_slice() {
            let res = digits::<_, (), (), _>(10).parse("0123456789");
            assert_eq!(res, (Some("0123456789"), Vec::new()));
        }

        #[test]
        fn parses_digits_into_vec() {
            let res = digits::<_, (), (), _>(16).parse("0123456789ABCDEF");
            assert_eq!(res, (Some(b"0123456789ABCDEF".to_vec()), Vec::new()));
        }

        #[test]
        fn parses_digits_from_non_static() {
            let string = String::from("f123456");
            let res = digits::<_, (), (), _>(7).parse(&string[1..]);
            assert_eq!(res, (Some("123456"), Vec::new()));
        }

        #[test]
        fn digits_with_others() {
            let input = "123 456 789 000";
            let res = digits::<_, (), (), _>(10)
                .padded()
                .repeated()
                .collect()
                .parse(input);

            assert_eq!(res, (Some(vec!["123", "456", "789", "000"]), Vec::new()));

            let input = "123 456 789 000";
            let res = digits::<_, (), (), _>(10)
                .padded()
                .map(|x: &str| x.parse())
                .unwrapped()
                .repeated()
                .collect()
                .parse(input);

            assert_eq!(res, (Some(vec![123_i32, 456, 789, 000,]), Vec::new()));
        }

        #[test]
        fn parses_int() {
            let res = int::<_, (), (), _>(10).parse("0123456789");
            assert_eq!(res, (Some("0".to_string()), Vec::new()));

            let res = int::<_, (), (), _>(10).parse("123456789");
            assert_eq!(res, (Some("123456789".to_string()), Vec::new()));
        }

        #[test]
        fn parses_int_into_slice() {
            let res = int::<_, (), (), _>(10).parse("0123456789");
            assert_eq!(res, (Some("0"), Vec::new()));

            let res = int::<_, (), (), _>(10).parse("123456789");
            assert_eq!(res, (Some("123456789"), Vec::new()));
        }

        #[test]
        fn parses_int_into_vec() {
            let res = int::<_, (), (), _>(16).parse("0123456789ABCDEF");
            assert_eq!(res, (Some(b"0".to_vec()), Vec::new()));

            let res = int::<_, (), (), _>(16).parse("123456789ABCDEF");
            assert_eq!(res, (Some(b"123456789ABCDEF".to_vec()), Vec::new()));
        }

        #[test]
        fn parses_int_from_non_static() {
            let string = String::from("f123456");
            let res = int::<_, (), (), _>(7).parse(&string[1..]);
            assert_eq!(res, (Some("123456"), Vec::new()));
        }

        #[test]
        fn int_with_others() {
            let input = "0 123 456 789 000";
            let res = int::<_, (), (), &'_ str>(10)
                .then_ignore(super::prelude::just(' '))
                .repeated()
                .collect()
                .parse(input);

            assert_eq!(res, (Some(vec!["0", "123", "456", "789"]), Vec::new()));

            let input = "0 123 456 789 000";
            let res = int::<_, (), (), _>(10)
                .padded()
                .map(|x: &str| x.parse())
                .unwrapped()
                .repeated()
                .collect()
                .parse(input);

            assert_eq!(res, (Some(vec![0, 123_i32, 456, 789, 0, 0, 0]), Vec::new()));
        }
    }
}
