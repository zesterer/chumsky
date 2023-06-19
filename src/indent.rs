//! Indentation-sensitive parsing.

use crate::{
    extra::ParserExtra,
    input::ValueInput,
    primitive::any,
    span::Span,
    text::{newline, Char},
    IterParser, Parser,
};

/// Parse semantic indentation.
pub fn semantic_indentation<'a, I, O, S, E, T, F>(
    token: T,
    make_group: F,
) -> impl Parser<'a, I, Vec<O>, E> + Clone
where
    I: ValueInput<'a, Token = char, Span = S>,
    S: Span,
    E: ParserExtra<'a, I>,
    T: Parser<'a, I, O, E> + Clone,
    F: Fn(Vec<O>, S) -> O + Clone,
{
    fn collapse<'a, O, S>(
        mut tree: Vec<(Vec<char>, Vec<O>, Option<S>)>,
        make_group: impl Fn(Vec<O>, S) -> O,
    ) -> Option<O> {
        while let Some((_, tts, line_span)) = tree.pop() {
            let tt = make_group(tts, line_span?);
            if let Some(last) = tree.last_mut() {
                last.1.push(tt);
            } else {
                return Some(tt);
            }
        }
        None
    }

    let line_ws = any().filter(|c: &char| c.is_inline_whitespace());

    let line = token
        .padded_by(line_ws.repeated().collect::<Vec<_>>())
        .repeated()
        .collect();

    let lines = line_ws
        .repeated()
        .collect::<Vec<char>>()
        .then(line.map_with_span(|line, span| (line, span)))
        .separated_by(newline())
        .collect::<Vec<_>>()
        .padded();

    lines.map(move |lines| {
        let mut nesting = vec![(Vec::new(), Vec::new(), None)];
        for (indent, (mut line, line_span)) in lines {
            let mut indent = indent.as_slice();
            let mut i = 0;
            while let Some(tail) = nesting
                .get(i)
                .and_then(|(n, _, _)| indent.strip_prefix(n.as_slice()))
            {
                indent = tail;
                i += 1;
            }
            if let Some(tail) = collapse(nesting.split_off(i), &make_group) {
                nesting.last_mut().unwrap().1.push(tail);
            }
            if !indent.is_empty() {
                nesting.push((indent.to_vec(), line, Some(line_span)));
            } else {
                nesting.last_mut().unwrap().1.append(&mut line);
            }
        }

        nesting.remove(0).1
    })
}
