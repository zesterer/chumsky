# Setting Up

Create a new project with `cargo new --bin foo`, add the latest version of Chumsky as a dependency, and place
the following in your `main.rs`:

```rust
use chumsky::prelude::*;

fn main() {
    let src = std::fs::read_to_string(std::env::args().nth(1).unwrap()).unwrap();

    println!("{}", src);
}
```

This code has one purpose: it treats the first command-line argument as a path, reads the corresponding file,
then prints the contents to the terminal. We don't really care for handling IO errors in this tutorial, so `.unwrap()`
will suffice.

Create a file named `test.foo` and run `cargo run -- test.foo` (the `--` tells cargo to pass the remaining
arguments to the program instead of cargo itself). You should see that the contents of `test.foo`, if any, get
printed to the console.

Next, we'll create a data type that represents a program written in Foo. All programs in Foo are expressions,
so we'll call it `Expr`.

```rust
#[derive(Debug)]
enum Expr {
    Num(f64),
    Var(String),

    Neg(Box<Expr>),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),

    Call(String, Vec<Expr>),
    Let {
        name: String,
        rhs: Box<Expr>,
        then: Box<Expr>,
    },
    Fn {
        name: String,
        args: Vec<String>,
        body: Box<Expr>,
        then: Box<Expr>,
    },
}
```

This is Foo's [Abstract Syntax Tree](https://en.wikipedia.org/wiki/Abstract_syntax_tree) (AST). It represents
all possible Foo programs and is defined recursively in terms of itself (`Box` is used to avoid the type being
infinitely large). Each expression may itself contain sub-expressions.

As an example, the expression `let x = 5; x * 3` is encoded as follows using the `Expr` type:

```rs
Expr::Let {
    name: "x",
    rhs: Expr::Num(5.0),
    then: Expr::Mul(
        Expr::Var("x"),
        Expr::Num(3.0),
    ),
}
```

The purpose of our parser will be to perform this conversion, from source code to AST.

We're also going to create a function that creates Foo's parser. Our parser takes in a `char` stream and
produces an `Expr`, so we'll use those types for the `I` (input) and `O` (output) type parameters.

```rust
fn parser() -> impl Parser<char, Expr, Error = Simple<char>> {
    // To be filled in later...
}
```

The `Error` associated type allows us to customise the error type that Chumsky uses. For now, we'll stick to
`Simple<I>`, a built-in error type that does everything we need.

In `main`, we'll alter the `println!` as follows:

```rust
println!("{:?}", parser().parse(src));
```

Now that all of the setup is complete that all of the setup is complete we can dive into getting the langauge.
