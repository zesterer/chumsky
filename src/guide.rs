// To generate docs with the guide, use `RUSTDOCFLAGS="--cfg docsrs" cargo +nightly doc --all-features`

#![doc = include_str!("../guide/intro.md")]
use super::*;

pub mod _00_getting_started {
    #![doc = include_str!("../guide/getting_started.md")]
    use super::*;
}

pub mod _01_key_concepts {
    #![doc = include_str!("../guide/key_concepts.md")]
    use super::*;
}

pub mod _02_meet_the_parsers {
    #![doc = include_str!("../guide/meet_the_parsers.md")]
    use super::*;
}

pub mod _03_error_and_recovery {
    #![doc = include_str!("../guide/error_and_recovery.md")]
    use super::*;
}

pub mod _04_recursion {
    #![doc = include_str!("../guide/recursion.md")]
    use super::*;
}

pub mod _05_debugging {
    #![doc = include_str!("../guide/debugging.md")]
    use super::*;
}

pub mod _06_technical_notes {
    #![doc = include_str!("../guide/technical_notes.md")]
    use super::*;
}

pub mod _07_tutorial {
    #![doc = include_str!("../guide/tutorial.md")]
    use super::*;
}
