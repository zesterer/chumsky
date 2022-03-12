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
}

#[derive(Clone)]
pub struct Padded<A> {
    pub(crate) parser: A,
}

impl<'a, I, E, S, A> Parser<'a, I, E, S> for Padded<A>
where
    I: Input + ?Sized,
    E: Error<I::Token>,
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
