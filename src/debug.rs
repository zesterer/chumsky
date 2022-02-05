//! Utilities for debugging parsers.
//!
//! *“He was staring at the instruments with the air of one who is trying to convert Fahrenheit to centigrade in his
//! head while his house is burning down.”*

use super::*;

use alloc::borrow::Cow;
use core::panic::Location;

/// Information about a specific parser.
#[allow(dead_code)]
pub struct ParserInfo {
    name: Cow<'static, str>,
    display: Rc<dyn fmt::Display>,
    location: Location<'static>,
}

impl ParserInfo {
    pub(crate) fn new(
        name: impl Into<Cow<'static, str>>,
        display: Rc<dyn fmt::Display>,
        location: Location<'static>,
    ) -> Self {
        Self {
            name: name.into(),
            display,
            location,
        }
    }
}

/// An event that occurred during parsing.
pub enum ParseEvent {
    /// Debugging information was emitted.
    Info(String),
}

/// A trait implemented by parser debuggers.
#[deprecated(
    note = "This trait is excluded from the semver guarantees of chumsky. If you decide to use it, broken builds are your fault."
)]
pub trait Debugger {
    /// Create a new debugging scope.
    fn scope<R, Info: FnOnce() -> ParserInfo, F: FnOnce(&mut Self) -> R>(
        &mut self,
        info: Info,
        f: F,
    ) -> R;
    /// Emit a parse event, if the debugger supports them.
    fn emit_with<F: FnOnce() -> ParseEvent>(&mut self, f: F);
    /// Invoke the given parser with a mode specific to this debugger.
    fn invoke<I: Clone, O, P: Parser<I, O> + ?Sized>(
        &mut self,
        parser: &P,
        stream: &mut StreamOf<I, P::Error>,
    ) -> PResult<I, O, P::Error>;
}

/// A verbose debugger that emits debugging messages to the console.
pub struct Verbose {
    // TODO: Don't use `Result`, that's silly
    events: Vec<Result<ParseEvent, (ParserInfo, Self)>>,
}

impl Verbose {
    pub(crate) fn new() -> Self {
        Self { events: Vec::new() }
    }

    #[allow(unused_variables)]
    fn print_inner(&self, depth: usize) {
        // a no-op on no_std!
        #[cfg(feature = "std")]
        for event in &self.events {
            for _ in 0..depth * 4 {
                print!(" ");
            }
            match event {
                Ok(ParseEvent::Info(s)) => println!("{}", s),
                Err((info, scope)) => {
                    println!(
                        "Entered {} at line {} in {}",
                        info.display,
                        info.location.line(),
                        info.location.file()
                    );
                    scope.print_inner(depth + 1);
                }
            }
        }
    }

    pub(crate) fn print(&self) {
        self.print_inner(0)
    }
}

impl Debugger for Verbose {
    fn scope<R, Info: FnOnce() -> ParserInfo, F: FnOnce(&mut Self) -> R>(
        &mut self,
        info: Info,
        f: F,
    ) -> R {
        let mut verbose = Verbose { events: Vec::new() };
        let res = f(&mut verbose);
        self.events.push(Err((info(), verbose)));
        res
    }

    fn emit_with<F: FnOnce() -> ParseEvent>(&mut self, f: F) {
        self.events.push(Ok(f()));
    }

    fn invoke<I: Clone, O, P: Parser<I, O> + ?Sized>(
        &mut self,
        parser: &P,
        stream: &mut StreamOf<I, P::Error>,
    ) -> PResult<I, O, P::Error> {
        parser.parse_inner_verbose(self, stream)
    }
}

/// A silent debugger that emits no debugging messages nor collects any debugging data.
pub struct Silent {
    phantom: PhantomData<()>,
}

impl Silent {
    pub(crate) fn new() -> Self {
        Self {
            phantom: PhantomData,
        }
    }
}

impl Debugger for Silent {
    fn scope<R, Info: FnOnce() -> ParserInfo, F: FnOnce(&mut Self) -> R>(
        &mut self,
        _: Info,
        f: F,
    ) -> R {
        f(self)
    }
    fn emit_with<F: FnOnce() -> ParseEvent>(&mut self, _: F) {}

    fn invoke<I: Clone, O, P: Parser<I, O> + ?Sized>(
        &mut self,
        parser: &P,
        stream: &mut StreamOf<I, P::Error>,
    ) -> PResult<I, O, P::Error> {
        parser.parse_inner_silent(self, stream)
    }
}
