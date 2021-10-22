use super::*;

use std::{
    borrow::Cow,
    panic::Location,
};

/// Information about a specific parser.
pub struct ParserInfo {
    #[allow(dead_code)]
    name: Cow<'static, str>,
    display: Rc<dyn fmt::Display>,
    location: Location<'static>,
}

impl ParserInfo {
    pub fn new(name: impl Into<Cow<'static, str>>, display: Rc<dyn fmt::Display>, location: Location<'static>) -> Self {
        Self {
            name: name.into(),
            display,
            location,
        }
    }
}

/// An event that occurred during parsing.
pub enum ParseEvent {
    Info(String),
}

pub trait Debugger {
    fn scope<R, Info: FnOnce() -> ParserInfo, F: FnOnce(&mut Self) -> R>(&mut self, info: Info, f: F) -> R;
    fn emit_with<F: FnOnce() -> ParseEvent>(&mut self, f: F);
    fn invoke<I: Clone, O, P: Parser<I, O> + ?Sized>(&mut self, parser: &P, stream: &mut StreamOf<I, P::Error>) -> PResult<I, O, P::Error>;
}

// Verbose

pub struct Verbose {
    // TODO: Don't use `Result`, that's silly
    events: Vec<Result<ParseEvent, (ParserInfo, Self)>>,
}

impl Verbose {
    pub(crate) fn new() -> Self {
        Self { events: Vec::new() }
    }

    fn print_inner(&self, depth: usize) {
        for event in &self.events {
            for _ in 0..depth * 4 { print!(" "); }
            match event {
                Ok(ParseEvent::Info(s)) => println!("{}", s),
                Err((info, scope)) => {
                    println!("Entered {} at line {} in {}", info.display, info.location.line(), info.location.file());
                    scope.print_inner(depth + 1);
                },
            }
        }
    }

    pub(crate) fn print(&self) { self.print_inner(0) }
}

impl Debugger for Verbose {
    fn scope<R, Info: FnOnce() -> ParserInfo, F: FnOnce(&mut Self) -> R>(&mut self, info: Info, f: F) -> R {
        let mut verbose = Verbose {
            events: Vec::new(),
        };
        let res = f(&mut verbose);
        self.events.push(Err((info(), verbose)));
        res
    }

    fn emit_with<F: FnOnce() -> ParseEvent>(&mut self, f: F) {
        self.events.push(Ok(f()));
    }

    fn invoke<I: Clone, O, P: Parser<I, O> + ?Sized>(&mut self, parser: &P, stream: &mut StreamOf<I, P::Error>) -> PResult<I, O, P::Error> {
        parser.parse_inner_verbose(self, stream)
    }
}

// Silent

pub struct Silent {
    phantom: PhantomData<()>,
}

impl Silent {
     pub(crate) fn new() -> Self { Self { phantom: PhantomData } }
}

impl Debugger for Silent {
    fn scope<R, Info: FnOnce() -> ParserInfo, F: FnOnce(&mut Self) -> R>(&mut self, _: Info, f: F) -> R { f(self) }
    fn emit_with<F: FnOnce() -> ParseEvent>(&mut self, _: F) {}

    fn invoke<I: Clone, O, P: Parser<I, O> + ?Sized>(&mut self, parser: &P, stream: &mut StreamOf<I, P::Error>) -> PResult<I, O, P::Error> {
        parser.parse_inner_silent(self, stream)
    }
}
