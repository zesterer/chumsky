// use chumsky::prelude::*;

// #[test]
// fn iter() {
//     fn parser<'a>() -> impl IterParser<'a, &'a str, char> {
//         any().repeated()
//     }

//     let mut chars = String::new();
//     for c in parser().parse_iter(&"abcdefg").into_result().unwrap() {
//         chars.push(c);
//     }

//     assert_eq!(&chars, "abcdefg");
// }
