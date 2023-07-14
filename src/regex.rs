//! Implementations of regex-based parsers

use super::*;
use regex_automata::{meta, Anchored, Input as ReInput};

/// See [`regex()`].
pub struct Regex<C: Char, I, E> {
    regex: meta::Regex,
    #[allow(dead_code)]
    phantom: EmptyPhantom<(C, E, I)>,
}

impl<C: Char, I, E> Clone for Regex<C, I, E> {
    fn clone(&self) -> Self {
        Self {
            regex: self.regex.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

/// Match input based on a provided regex pattern
pub fn regex<C: Char, I, E>(pattern: &str) -> Regex<C, I, E> {
    Regex {
        regex: meta::Regex::new(pattern).expect("Failed to compile regex"),
        phantom: EmptyPhantom::new(),
    }
}

impl<'a, C, I, E> ParserSealed<'a, I, &'a C::Str, E> for Regex<C, I, E>
where
    C: Char,
    I: StrInput<'a, C>,
    E: ParserExtra<'a, I>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, &'a C::Str> {
        let before = inp.offset();

        let re_in = ReInput::new(inp.full_slice())
            .anchored(Anchored::Yes)
            .range(before.offset..);

        let res = self.regex.find(re_in).map(|m| m.len());

        match res {
            Some(len) => {
                let before = inp.offset();
                inp.skip_bytes(len);
                let after = inp.offset();
                Ok(M::bind(|| inp.slice_inner(before.offset..after.offset)))
            }
            None => {
                // TODO: Improve error
                inp.add_alt(inp.offset().offset, None, None, inp.span_since(before));
                Err(())
            }
        }
    }

    go_extra!(&'a C::Str);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn regex_parser() {
        use self::prelude::*;
        use self::regex::*;

        fn parser<'a, C: Char, I: StrInput<'a, C>>() -> impl Parser<'a, I, Vec<&'a C::Str>> {
            regex("[a-zA-Z_][a-zA-Z0-9_]*")
                .padded()
                .repeated()
                .collect()
        }
        assert_eq!(
            parser().parse("hello world this works").into_result(),
            Ok(vec!["hello", "world", "this", "works"]),
        );

        assert_eq!(
            parser()
                .parse(b"hello world this works" as &[_])
                .into_result(),
            Ok(vec![
                b"hello" as &[_],
                b"world" as &[_],
                b"this" as &[_],
                b"works" as &[_],
            ]),
        );
    }
}
