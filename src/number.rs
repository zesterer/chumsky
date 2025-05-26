//! TODO: Add documentation when approved

use super::*;
pub use lexical::format;

use lexical::parse_partial;
use lexical::FromLexical;

/// TODO: Add documentation when approved
pub struct Number<const F: u128, I, O, E> {
    #[allow(dead_code)]
    phantom: EmptyPhantom<(I, E, O)>,
}

impl<const F: u128, I, O, E> Copy for Number<F, I, O, E> {}
impl<const F: u128, I, O, E> Clone for Number<F, I, O, E> {
    fn clone(&self) -> Self {
        *self
    }
}

/// TODO: Add documentation when approved
pub const fn number<const F: u128, I, O, E>() -> Number<F, I, O, E> {
    Number::<F, I, O, E> {
        phantom: EmptyPhantom::new(),
    }
}

/// A label denoting a parseable number.
pub struct ExpectedNumber;

impl<'src, const F: u128, I, O, E> Parser<'src, I, O, E> for Number<F, I, O, E>
where
    O: FromLexical,
    I: SliceInput<'src, Cursor = usize>,
    <I as SliceInput<'src>>::Slice: AsRef<[u8]>,
    E: ParserExtra<'src, I>,
    E::Error: LabelError<'src, I, ExpectedNumber>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'src, '_, I, E>) -> PResult<M, O> {
        let before = inp.cursor();
        match parse_partial(inp.slice_trailing_inner().as_ref()) {
            Ok((out, skip)) => {
                // SAFETY: `skip` is no longer than the trailing input's byte length
                unsafe { inp.skip_bytes(skip) };
                Ok(M::bind(|| out))
            }
            Err(_err) => {
                // TODO: Improve error
                let span = inp.span_since(&before);
                inp.add_alt([ExpectedNumber], None, span);
                Err(())
            }
        }
    }

    go_extra!(O);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{extra, Parser};
    use lexical::format::RUST_LITERAL;

    // These have been shamelessly yanked from the rust test-float-parse suite.
    // More specifically:
    //
    // https://github.com/rust-lang/rust/tree/64185f205dcbd8db255ad6674e43c63423f2369a/src/etc/test-float-parse
    mod rust {
        use super::*;

        const FLOAT: Number<RUST_LITERAL, &str, f64, extra::Default> = number();

        fn validate(test: &str) {
            FLOAT.parse(test).unwrap();
        }

        #[test]
        fn few_ones() {
            let mut pow = vec![];
            for i in 0..63 {
                pow.push(1u64 << i);
            }
            for a in &pow {
                for b in &pow {
                    for c in &pow {
                        validate(&(a | b | c).to_string());
                    }
                }
            }
        }

        #[test]
        fn huge_pow10() {
            for e in 300..310 {
                for i in 0..100000 {
                    validate(&format!("{i}e{e}"));
                }
            }
        }

        #[test]
        fn long_fraction() {
            for n in 0..10 {
                let digit = char::from_digit(n, 10).unwrap();
                let mut s = "0.".to_string();
                for _ in 0..400 {
                    s.push(digit);
                    if s.parse::<f64>().is_ok() {
                        validate(&s);
                    }
                }
            }
        }

        #[test]
        fn short_decimals() {
            for e in 1..301 {
                for i in 0..10000 {
                    if i % 10 == 0 {
                        continue;
                    }

                    validate(&format!("{i}e{e}"));
                    validate(&format!("{i}e-{e}"));
                }
            }
        }

        #[test]
        fn subnorm() {
            for bits in 0u32..(1 << 21) {
                let single: f32 = f32::from_bits(bits);
                validate(&format!("{single:e}"));
                let double: f64 = f64::from_bits(bits as u64);
                validate(&format!("{double:e}"));
            }
        }

        #[test]
        fn tiny_pow10() {
            for e in 301..327 {
                for i in 0..100000 {
                    validate(&format!("{i}e-{e}"));
                }
            }
        }

        #[test]
        fn u32_small() {
            for i in 0..(1 << 19) {
                validate(&i.to_string());
            }
        }

        #[test]
        fn u64_pow2() {
            for exp in 19..64 {
                let power: u64 = 1 << exp;
                validate(&power.to_string());
                for offset in 1..123 {
                    validate(&(power + offset).to_string());
                    validate(&(power - offset).to_string());
                }
            }
            for offset in 0..123 {
                validate(&(u64::MAX - offset).to_string());
            }
        }
    }
}
