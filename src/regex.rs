//! Implementations of regex-based parsers

use super::*;

/// See [`regex`].
pub struct Regex<C: Char, I: ?Sized, E> {
    regex: C::Regex,
    phantom: PhantomData<(E, I)>,
}

/// Match input based on a provided regex pattern
pub fn regex<C: Char, I, E>(pattern: &str) -> Regex<C, I, E> {
    Regex {
        regex: C::new_regex(pattern),
        phantom: PhantomData,
    }
}

impl<'a, C, I, E> Parser<'a, I, &'a C::Str, E> for Regex<C, I, E>
where
    C: Char,
    I: StrInput<'a, C>,
    E: ParserExtra<'a, I>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, &'a C::Str> {
        let before = inp.offset();
        match C::match_regex(&self.regex, inp.slice_trailing()) {
            Some(len) => {
                let before = inp.offset();
                inp.skip_bytes(len);
                let after = inp.offset();
                Ok(M::bind(|| inp.slice(before..after)))
            }
            None => {
                // TODO: Improve error
                inp.add_alt(Located::at(
                    inp.offset().into(),
                    // SAFETY: Using offsets derived from input
                    E::Error::expected_found(None, None, unsafe { inp.span_since(before) }),
                ));
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
