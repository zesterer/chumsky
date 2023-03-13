// To generate docs with the guide, use `RUSTDOCFLAGS="--cfg docsrs" cargo +nightly doc --all-features`

#![doc = include_str!("../guide/intro.md")]
use super::*;

pub mod getting_started {
    #![doc = include_str!("../guide/getting_started.md")]
    use super::*;
}

pub mod key_concepts {
    #![doc = include_str!("../guide/key_concepts.md")]
    use super::*;
}

pub mod meet_the_parsers {
    #![doc = include_str!("../guide/meet_the_parsers.md")]
    use super::*;
}

pub mod technical_notes {
    #![doc = include_str!("../guide/technical_notes.md")]
    use super::*;
}
