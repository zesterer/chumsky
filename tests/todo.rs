use chumsky::prelude::*;

#[test]
#[should_panic]
fn todo_err() {
    let expr = todo::<&str, String, extra::Default>();
    expr.then_ignore(end()).parse("a+b+c");
}
