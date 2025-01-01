//! Implementations of regex-based parsers

use super::*;
use regex_automata::{meta, Anchored, Input as ReInput};

/// See [`regex()`].
pub struct Regex<I, E> {
    regex: meta::Regex,
    #[allow(dead_code)]
    phantom: EmptyPhantom<(E, I)>,
}

impl<I, E> Clone for Regex<I, E> {
    fn clone(&self) -> Self {
        Self {
            regex: self.regex.clone(),
            phantom: EmptyPhantom::new(),
        }
    }
}

/// Match input based on a provided regex pattern
pub fn regex<I, E>(pattern: &str) -> Regex<I, E> {
    Regex {
        regex: meta::Regex::new(pattern).expect("Failed to compile regex"),
        phantom: EmptyPhantom::new(),
    }
}

impl<'src, S, I, E> Parser<'src, I, &'src S, E> for Regex<I, E>
where
    I: StrInput<'src, Slice = &'src S>,
    I::Token: Char,
    S: ?Sized + AsRef<[u8]> + 'src,
    E: ParserExtra<'src, I>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, &'src S> {
        let before = inp.cursor();

        let re_in = ReInput::new(inp.full_slice())
            .anchored(Anchored::Yes)
            .range(before.inner..);

        let res = self.regex.find(re_in).map(|m| m.len());

        match res {
            Some(len) => {
                let before = inp.cursor();
                // SAFETY: `len` *must* be no greater than the byte length of the remaining string
                unsafe {
                    inp.skip_bytes(len);
                }
                let after = inp.cursor();
                Ok(M::bind(|| inp.slice(&before..&after)))
            }
            None => {
                // TODO: Improve error
                let span = inp.span_since(&before);
                inp.add_alt([DefaultExpected::SomethingElse], None, span);
                Err(())
            }
        }
    }

    go_extra!(&'src S);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn regex_parser() {
        use self::prelude::*;
        use self::regex::*;

        fn parser<'src, S, I>() -> impl Parser<'src, I, Vec<&'src S>>
        where
            S: ?Sized + AsRef<[u8]> + 'src,
            I: StrInput<'src, Slice = &'src S>,
            I::Token: Char,
        {
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
