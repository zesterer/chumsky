# Functions

We're almost at a complete implementation of Foo. There's just one thing left: *functions*.

Surprisingly, parsing functions is the easy part. All we need to modify is the definition of `decl` to add `r#fn`. It
looks very much like the existing definition of `r#let`:

```rust
let decl = recursive(|decl| {
    let r#let = text::keyword("let")
        .ignore_then(ident)
        .then_ignore(just('='))
        .then(expr.clone())
        .then_ignore(just(';'))
        .then(decl.clone())
        .map(|((name, rhs), then)| Expr::Let {
            name,
            rhs: Box::new(rhs),
            then: Box::new(then),
        });

    let r#fn = text::keyword("fn")
        .ignore_then(ident)
        .then(ident.repeated())
        .then_ignore(just('='))
        .then(expr.clone())
        .then_ignore(just(';'))
        .then(decl)
        .map(|(((name, args), body), then)| Expr::Fn {
            name,
            args,
            body: Box::new(body),
            then: Box::new(then),
        });

    r#let
        .or(r#fn)
        .or(expr)
        .padded()
});
```

There's nothing new here, you understand this all already.

Obviously, we also need to add support for *calling* functions by modifying `atom`:

```rust
let call = ident
    .then(expr.clone()
        .separated_by(just(','))
        .allow_trailing() // Foo is Rust-like, so allow trailing commas to appear in arg lists
        .delimited_by(just('('), just(')')))
    .map(|(f, args)| Expr::Call(f, args));

let atom = int
    .or(expr.delimited_by(just('('), just(')')))
    .or(call)
    .or(ident.map(Expr::Var));
```

The only new combinator here is `separated_by` which behaves like `repeated`, but requires a separator pattern between
each element. It has a method called `allow_trailing` which allows for parsing a trailing separator at the end of the
elements.

Next, we modify our `eval` function to support a function stack.

```rust
fn eval<'a>(
    expr: &'a Expr,
    vars: &mut Vec<(&'a String, f64)>,
    funcs: &mut Vec<(&'a String, &'a [String], &'a Expr)>,
) -> Result<f64, String> {
    match expr {
        Expr::Num(x) => Ok(*x),
        Expr::Neg(a) => Ok(-eval(a, vars, funcs)?),
        Expr::Add(a, b) => Ok(eval(a, vars, funcs)? + eval(b, vars, funcs)?),
        Expr::Sub(a, b) => Ok(eval(a, vars, funcs)? - eval(b, vars, funcs)?),
        Expr::Mul(a, b) => Ok(eval(a, vars, funcs)? * eval(b, vars, funcs)?),
        Expr::Div(a, b) => Ok(eval(a, vars, funcs)? / eval(b, vars, funcs)?),
        Expr::Var(name) => if let Some((_, val)) = vars.iter().rev().find(|(var, _)| *var == name) {
            Ok(*val)
        } else {
            Err(format!("Cannot find variable `{}` in scope", name))
        },
        Expr::Let { name, rhs, then } => {
            let rhs = eval(rhs, vars, funcs)?;
            vars.push((name, rhs));
            let output = eval(then, vars, funcs);
            vars.pop();
            output
        },
        Expr::Call(name, args) => if let Some((_, arg_names, body)) = funcs
            .iter()
            .rev()
            .find(|(var, _, _)| *var == name)
            .copied()
        {
            if arg_names.len() == args.len() {
                let mut args = args
                    .iter()
                    .map(|arg| eval(arg, vars, funcs))
                    .zip(arg_names.iter())
                    .map(|(val, name)| Ok((name, val?)))
                    .collect::<Result<_, String>>()?;
                vars.append(&mut args);
                let output = eval(body, vars, funcs);
                vars.truncate(vars.len() - args.len());
                output
            } else {
                Err(format!(
                    "Wrong number of arguments for function `{}`: expected {}, found {}",
                    name,
                    arg_names.len(),
                    args.len(),
                ))
            }
        } else {
            Err(format!("Cannot find function `{}` in scope", name))
        },
        Expr::Fn { name, args, body, then } => {
            funcs.push((name, args, body));
            let output = eval(then, vars, funcs);
            funcs.pop();
            output
        },
    }
}
```

Another big change! On closer inspection, however, this looks a lot like the change we made previously when we added
support for `let` declarations. Whenever we encounter an `Expr::Fn`, we just push the function to the `funcs` stack and
continue. Whenever we encounter an `Expr::Call`, we search the function stack backwards, as we did for variables, and
then execute the body of the function (making sure to evaluate and push the arguments!).

As before, we'll need to change the `eval` call in `main` to:

```rust
eval(&ast, &mut Vec::new(), &mut Vec::new())
```

Give the interpreter a test - see what you can do with it! Here's an example program to get you started:

```
let five = 5;
let eight = 3 + five;
fn add x y = x + y;
add(five, eight)
```