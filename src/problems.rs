//! TODO

use crate::visit::{ParserInfo, ParserVisitor, Visitable};

#[derive(Clone, PartialEq)]
enum CheckState {
    None,
    Check(String),
    Defer(String),
}

struct ProblemVisitor {
    problems: Vec<String>,

    first: bool,
    check_nonempty: CheckState,
}

impl ProblemVisitor {
    fn new() -> Self {
        ProblemVisitor {
            problems: Vec::new(),

            first: true,
            check_nonempty: CheckState::None,
        }
    }

    fn into_problems(self) -> Vec<String> {
        self.problems
    }
}

impl ParserVisitor for ProblemVisitor {
    fn visit<P>(&mut self, info: &ParserInfo<'_, P>)
    where
        P: ?Sized + Visitable,
    {
        if self.first {
            self.first = false;
            if info.size_hint.lower() == 0 {
                self.problems.push(format!(
                    "The top-level `{}` parser can potentially consume no input, meaning that it cannot fail.\nThis is probably a bug.\nConsider adding `.then_ignore(end())` to the parser.", info.name
                ))
            }
        }

        let state = core::mem::replace(&mut self.check_nonempty, CheckState::None);
        if let CheckState::Check(name) = state {
            if info.size_hint.lower() == 0 {
                self.problems.push(format!(
                    "`{}` parser has an inner parser that can potentially consume no input, meaning that it cannot fail.\nThis is probably a bug, because it could lead to an infinite loop.\nConsider using `.at_least(1)` to force the inner parser to consume some input.",
                    name,
                ))
            }
            self.check_nonempty = CheckState::Defer(name);
        }

        match info.name {
            "repeated" | "separated_by" => {
                let old = core::mem::replace(
                    &mut self.check_nonempty,
                    CheckState::Check(info.name.to_string())
                );
                info.visit(self);
                self.check_nonempty = old;
            }
            _ => info.visit(self),
        }

        let state = core::mem::replace(&mut self.check_nonempty, CheckState::None);
        if let CheckState::Defer(name) = state {
            self.check_nonempty = CheckState::Check(name);
        }
    }
}

/// TODO
pub trait Problems: Visitable {
    /// TODO
    fn find_problems(&self) -> Vec<String>;
}

impl<P: Visitable> Problems for P {
    fn find_problems(&self) -> Vec<String> {
        let mut visitor = ProblemVisitor::new();
        self.visit(&mut visitor);
        visitor.into_problems()
    }
}
