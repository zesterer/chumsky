# Assignments

Our next step is to handle `let`. Unlike Rust and other imperative languages, `let` in Foo is an expression and not an
statement (Foo has no statements) that takes the following form:

```
let <ident> = <expr>; <expr>
```

We only want `let`s to appear at the outermost level of the expression, so we leave it out of the original recursive
expression definition. However, we also want to be able to chain `let`s together, so we put them in their own recursive
definition. We call it `decl` ('declaration') because we're eventually going to be adding `fn` syntax too.

```rust
let ident = text::ident()
    .padded();

let expr = recursive(|expr| {
    let int = text::int(10)
        .map(|s: String| Expr::Num(s.parse().unwrap()))
        .padded();

    let atom = int
        .or(expr.delimited_by(just('('), just(')')))
        .or(ident.map(Expr::Var));

    let op = |c| just(c).padded();

    let unary = op('-')
        .repeated()
        .then(atom)
        .foldr(|_op, rhs| Expr::Neg(Box::new(rhs)));

    let product = unary.clone()
        .then(op('*').to(Expr::Mul as fn(_, _) -> _)
            .or(op('/').to(Expr::Div as fn(_, _) -> _))
            .then(unary)
            .repeated())
        .foldl(|lhs, (op, rhs)| op(Box::new(lhs), Box::new(rhs)));

    let sum = product.clone()
        .then(op('+').to(Expr::Add as fn(_, _) -> _)
            .or(op('-').to(Expr::Sub as fn(_, _) -> _))
            .then(product)
            .repeated())
        .foldl(|lhs, (op, rhs)| op(Box::new(lhs), Box::new(rhs)));

    sum
});

let decl = recursive(|decl| {
    let r#let = text::keyword("let")
        .ignore_then(ident)
        .then_ignore(just('='))
        .then(expr.clone())
        .then_ignore(just(';'))
        .then(decl)
        .map(|((name, rhs), then)| Expr::Let {
            name,
            rhs: Box::new(rhs),
            then: Box::new(then),
        });

    r#let
        // Must be later in the chain than `r#let` to avoid ambiguity
        .or(expr)
        .padded()
});

decl
    .then_ignore(end())
```

`keyword` is simply a parser that looks for an exact identifier (i.e: it doesn't match identifiers that only start with
a keyword).

Other than that, there's nothing in the definition of `r#let` that you haven't seen before: familiar combinators, but
combined in different ways. It selectively ignores parts of the syntax that we don't care about after validating that
it exists, then uses those elements that it does care about to create an `Expr::Let` AST node.

Another thing to note is that the definition of `ident` will parse `"let"`. To avoid the parser accidentally deciding
that `"let"` is a variable, we place `r#let` earlier in the or chain than `expr` so that it prioritises the correct
interpretation. As mentioned in previous sections, Chumsky handles ambiguity simply by choosing the first successful
parse it encounters, so making sure that we declare things in the right order can sometimes be important.

You should now be able to run the interpreter and have it accept an input such as

```
let five = 5;
five * 3
```

Unfortunately, the `eval` function will panic because we've not yet handled `Expr::Var` or `Expr::Let`. Let's do that
now.

```rust
fn eval<'a>(expr: &'a Expr, vars: &mut Vec<(&'a String, f64)>) -> Result<f64, String> {
    match expr {
        Expr::Num(x) => Ok(*x),
        Expr::Neg(a) => Ok(-eval(a, vars)?),
        Expr::Add(a, b) => Ok(eval(a, vars)? + eval(b, vars)?),
        Expr::Sub(a, b) => Ok(eval(a, vars)? - eval(b, vars)?),
        Expr::Mul(a, b) => Ok(eval(a, vars)? * eval(b, vars)?),
        Expr::Div(a, b) => Ok(eval(a, vars)? / eval(b, vars)?),
        Expr::Var(name) => if let Some((_, val)) = vars.iter().rev().find(|(var, _)| *var == name) {
            Ok(*val)
        } else {
            Err(format!("Cannot find variable `{}` in scope", name))
        },
        Expr::Let { name, rhs, then } => {
            let rhs = eval(rhs, vars)?;
            vars.push((name, rhs));
            let output = eval(then, vars);
            vars.pop();
            output
        },
        _ => todo!(),
    }
}
```

Woo! That got a bit more complicated. Don't fear, there are only 3 important changes:

1. Because we need to keep track of variables that were previously defined, we use a `Vec` to remember them. Because
   `eval` is a recursive function, we also need to pass is to all recursive calls.

2. When we encounter an `Expr::Let`, we first evaluate the right-hand side (`rhs`). Once evaluated, we push it to the
   `vars` stack and evaluate the trailing `then` expression (i.e: all of the remaining code that appears after the
   semicolon). Popping it afterwards is not *technically* necessary because Foo does not permit nested declarations,
   but we do it anyway because it's good practice and it's what we'd want to do if we ever decided to add nesting.

3. When we encounter an `Expr::Var` (i.e: an inline variable) we search the stack *backwards* (because Foo permits
   [variable shadowing](https://en.wikipedia.org/wiki/Variable_shadowing) and we only want to find the most recently
   declared variable with the same name) to find the variables's value. If we can't find a variable of that name, we
   generate a runtime error which gets propagated back up the stack.

Obviously, the signature of `eval` has changed so we'll update the call in `main` to become:

```rust
eval(&ast, &mut Vec::new())
```

Make sure to test the interpreter. Try experimenting with `let` declarations to make sure things aren't broken. In
particular, it's worth testing variable shadowing by ensuring that the following program produces `8`:

```
let x = 5;
let x = 3 + x;
x
```

