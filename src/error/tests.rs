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
    },
    indoc! {
        r#"
        found end of input
        "#
    }
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
    },
    indoc! {
        r#"
        found end of input
        "#
    }
)]
#[test_case(
    // This case represents a bug, and the expected output should include the custom error.
    Simple {
        span: 0..0,
        reason: Custom("CUSTOM_ERROR".to_string()),
        expected: HashSet::default(),
        found: None,
        label: None,
    },
    indoc! {
        r#"
        found end of input
        "#
    }
)]
#[test_case(
    Simple {
        span: 0..0,
        reason: Unexpected,
        expected: make_expected([None]),
        found: Some('x'),
        label: None,
    },
    indoc! {
        r#"
        found "x" but expected end of input
        "#
    }
)]
#[test_case(
    Simple {
        span: 0..0,
        reason: Unexpected,
        expected: make_expected(['x']),
        found: None,
        label: None,
    },
    indoc! {
        r#"
        found end of input but expected "x"
        "#
    }
)]
#[test_case(
    Simple {
        span: 0..0,
        reason: Unexpected,
        expected: make_expected(['x', 'y']),
        found: None,
        label: None,
    },
    indoc! {
        r#"
        found end of input but expected either "x" or "y"
        "#
    }
)]
#[test_case(
    Simple {
        span: 0..0,
        reason: Unexpected,
        expected: make_expected([None, Some('x')]),
        found: Some('y'),
        label: None,
    },
    indoc! {
        r#"
        found "y" but expected either "x" or end of input
        "#
    }
)]
#[test_case(
    Simple {
        span: 0..0,
        reason: Unexpected,
        expected: make_expected(['x', 'y', 'z']),
        found: None,
        label: None,
    },
    indoc! {
        r#"
        found end of input but expected one of "x", "y", or "z"
        "#
    }
)]
#[test_case(
    Simple {
        span: 0..0,
        reason: Unexpected,
        expected: make_expected([Some('x'), Some('y'), None]),
        found: Some('z'),
        label: None,
    },
    indoc! {
        r#"
        found "z" but expected one of "x", "y", or end of input
        "#
    }
)]
fn error_display(s: Simple<char>, expected: &str) {
    let actual = s.to_string();
    let expected = expected.trim_end();
    assert_eq!(
        expected, &actual,
        "\n= Expected =\n{}\n= Actual =\n{}",
        expected, &actual,
    );
}

fn make_expected<I, T>(alternatives: I) -> HashSet<Option<char>, crate::error::RandomState>
where
    I: IntoIterator<Item = T>,
    T: Into<Option<char>>,
{
    alternatives.into_iter().map(|x| x.into()).collect()
}
