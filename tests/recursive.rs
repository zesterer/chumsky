use chumsky::prelude::*;

#[test]
#[should_panic]
fn recursive_define_twice() {
    let mut expr = Recursive::declare();
    expr.define({
        let atom = any::<&str, extra::Default>()
            .filter(|c: &char| c.is_alphabetic())
            .repeated()
            .at_least(1)
            .collect();
        let sum = expr
            .clone()
            .then_ignore(just('+'))
            .then(expr.clone())
            .map(|(a, b)| format!("{}{}", a, b));

        sum.or(atom)
    });
    expr.define(expr.clone());

    expr.then_ignore(end()).parse("a+b+c");
}
