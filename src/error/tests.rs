use crate::error::Simple;
use crate::error::SimpleReason::*;
use indoc::indoc;
use std::collections::HashSet;
use test_case::test_case;

#[test_case(
    Simple {
        span: 0..0,
        reason: Unexpected,
        expected: HashSet::default(),
        found: None,
        label: None,
    }
    => indoc! {
        r#"
        found end of input
        "#
    }.trim_end().to_string()
)]
#[test_case(
    Simple {
        span: 0..0,
        reason: Unclosed {
            span: 0..0,
            delimiter: '(',
        },
        expected: HashSet::default(),
        found: None,
        label: None,
    }
    => indoc! {
        r#"
        found end of input
        "#
    }.trim_end().to_string()
)]
#[test_case(
    Simple {
        span: 0..0,
        reason: Custom("CUSTOM_ERROR".to_string()),
        expected: HashSet::default(),
        found: None,
        label: None,
    }
    => indoc! {
        r#"
        found end of input
        "#
    }.trim_end().to_string()
)]
#[test_case(
    Simple {
        span: 0..0,
        reason: Unexpected,
        expected: make_expected(['x', 'y']),
        found: None,
        label: None,
    }
    => indoc! {
        r#"
        found end of input but expected one of "x", "y"
        "#
    }.trim_end().to_string()
)]
fn error_display(s: Simple<char>) -> String {
    s.to_string()
}

fn make_expected<I, T>(alternatives: I) -> HashSet<Option<char>, crate::error::RandomState>
where
    I: IntoIterator<Item = T>,
    T: Into<Option<char>>,
{
    alternatives.into_iter().map(|x| x.into()).collect()
}
