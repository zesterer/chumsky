//! TODO: Add documentation when approved

pub use lexical::format;

use crate::extra::ParserExtra;
use crate::input::{InputRef, SliceInput};
use crate::private::{Check, Emit, Mode, PResult, ParserSealed};
use crate::EmptyPhantom;

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

impl<'a, const F: u128, I, O, E> ParserSealed<'a, I, O, E> for Number<F, I, O, E>
where
    O: FromLexical,
    I: SliceInput<'a, Offset = usize>,
    <I as SliceInput<'a>>::Slice: AsRef<[u8]>,
    E: ParserExtra<'a, I>,
{
    #[inline]
    fn go<M: Mode>(&self, inp: &mut InputRef<'a, '_, I, E>) -> PResult<M, O> {
        let before = inp.offset();
        match parse_partial(inp.slice_trailing_inner().as_ref()) {
            Ok((out, skip)) => {
                inp.skip_bytes(skip);
                Ok(M::bind(|| out))
            }
            Err(_err) => {
                // TODO: Improve error
                inp.add_alt(inp.offset().offset, None, None, inp.span_since(before));
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
                    validate(&format!("{}e{}", i, e));
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

                    validate(&format!("{}e{}", i, e));
                    validate(&format!("{}e-{}", i, e));
                }
            }
        }

        #[test]
        fn subnorm() {
            for bits in 0u32..(1 << 21) {
                let single: f32 = unsafe { core::mem::transmute(bits) };
                validate(&format!("{:e}", single));
                let double: f64 = unsafe { core::mem::transmute(bits as u64) };
                validate(&format!("{:e}", double));
            }
        }

        #[test]
        fn tiny_pow10() {
            for e in 301..327 {
                for i in 0..100000 {
                    validate(&format!("{}e-{}", i, e));
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
