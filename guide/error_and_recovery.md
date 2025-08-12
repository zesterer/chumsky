# Error And Recovery

A key property of parsing unstructured data into a more structured, semantic form, is that that unstructured data may not be correctly arranged such that the conversion is possible. While this happens with (basically) any parser, different parsers might have different expectations of how much they want to do to recover from or provide info on malformed data. A network-facing protocol parser might decide that it just needs to know that something bad happened, while a programming language compiler might want to ponder on the data and its surrounding context and provide as much information as possible to the end user, which might itself involve going over *more* data instead of failing immediately. Certain categories of errors may even be entirely recoverable from!

## What is an [`Error`]?

Chumsky manages the tracking and generation of errors for you. However, you may customise what information an error keeps track of (and how) by changing the error type (see [extra::Err]). Chumsky provides a range of built-in error types to handle a range of use-cases, but you can also implement the [Error] trait for your own error type if you want even more fine-grained control.

### The Quintessential Quadruplet of Errors

For prototyping and modest use cases, Chumsky provides 4 separate built-in types that implement [`Error`], ranging from a super cheap ZeroSizedType (ZST) to a complex and detailed user-centric error. Instances of these types can be modified to alter their contained data, such as altering the expected value of an expression, the span where the failure ocurred, or by providing an arbitrary context as in [`Rich`].

- [`EmptyErr`]: the ZST defaulted to in most situations, it contains no additional information other than that an error has occurred, but also very minimal overhead. Useful in high performance environments where error recovery may not be viable or performance concerns are more significant than usability concerns.

- [`Cheap`]: contains only [`Span`] information about the associated error, letting you know where it happened, but not giving you much more information besides. As the name implies, it is very cheap, and thus usable for high performance environments where basic usability is still nice to have.

- [`Simple`]: contains the [`Span`], but also the found token at the location of the error. This error is a good middle ground between the raw speed of [`Cheap`] and the detailed user-centric focus of [`Rich`], while still being able to satisfy medium performance requirements.

- [`Rich`]: the recommended type for dealing with user input at the expense of raw speed. Rich is still *fast* for applications like compilers and interpreters, and a great choice if you want to give users a pleasant editing experience first and foremost. Rich error types contain [`Span`] information as well as found and expected values, a label to describe the associated parser construction, the ability to merge errors in the same span, as well as a potential context with truly arbitrary data.

## The [`Span`] Trait

Spans are an important feature of any competent parser. They provide a location within a source file, denoted with start and end offsets, that corresponds to the location of some element within the source code (often a single character or token, but also an entire multi-token high-level structure like an expression, statement, or function).

Relevant to this section, spans are also used as an input to parser errors, allowing the final message shown to the user to reference the location at which an error occurred, along with other contextual information (such as which structure the error occurred within).

## Recovering from an [`Error`]

We can summarize recovery into three simple steps:

- *Report* the error accurately.
- *Resynchronize* with the input stream, finding a point where parsing can likely resume.
- *Resume* parsing along the input stream, capturing more errors or gracefully recovering and continuing execution.

This approach yields significant benefits, it allows us to generate multiple errors per each run of our parser, which means less back and forth with the user. It also allows us to capture more information at any one time, enhancing the interpretability of errors and the ability for us to augment their context with useful information for resolving them. Furthermore, even if parts of the input are invalid, we may often be able to reconstruct a partial subset of our input, aiding in subsequent analysis or tooling.

Because errors inherently deal with **invalid** input, any action taken to resolve them is essentially an educated guess on the part of the parser's developer. For this reason, a Recovery Strategy's effectiveness is highly dependent on being able to tradeoff the risk of encountering continued malformity from the same error with not skipping **too** much data. If we fail on the former, we end up reporting "noise" errors that are solved more easily than the parser may think, and if we fail on the latter we force the user to restart our parser multiple times to deal with any unstructured input.

In the next section we'll see how to define custom Recovery Strategies for our parsers.

### Recovery Strategies are also Parsers!

A Recovery Strategy is nothing more than a parser expression to be called in exceptional conditions, Consider the following code:

```ignore
#[derive(Clone, Debug, PartialEq, Eq)]
enum ErrorKind {
    UnexpectedText(String),
    Unknown,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Expr {
    Error(ErrorKind),
    Int(i64),
    List(Vec<Expr>),
}

pub fn lexer<'src>() -> impl Parser<'src, &'src str, Expr, extra::Err<Rich<'src, char>>> {
    // Atoms.
    let int = text::int(10).from_str().map(|r| match r {
        Ok(int) => Expr::Int(int),
        Err(_) => Expr::Error(ErrorKind::Unknown),
    });

    // Errors.
    let text_recovery = any()
        .filter(|c: &char| c.is_ascii_alphabetic())
        .repeated()
        .at_least(1)
        .collect::<String>()
        .map(|s| ErrorKind::UnexpectedText(s));
    let naive_recovery = just('[')
        .then(none_of(']').repeated().then(just(']')))
        .map(|_| ErrorKind::Unknown);

    recursive(|expr| {
        expr.separated_by(just(','))
            .collect::<Vec<_>>()
            .delimited_by(just('['), just(']'))
            .map(Expr::List)
            // If parsing a list expression fails, guess at the error being accidental text input.
            .recover_with(via_parser(text_recovery.map(Expr::Error)))
            .or(int)
            // Fallback to less conservative recovery otherwise.
            .recover_with(via_parser(naive_recovery.map(Expr::Error)))
            .padded()
    })
}

// Naive recovery strategy gives us little information...
assert_eq!(
    lexer().parse("[[💥, two], [💥, 4]]").output(),
    Some(&Expr::List(vec![
        Expr::Error(ErrorKind::Unknown),
        Expr::Error(ErrorKind::Unknown)
    ]))
);

// But more specific strategies allow us to extract more and better information!
assert_eq!(
    lexer().parse("[[1, two], [three, 4]]").output(),
    Some(&Expr::List(vec![
        Expr::List(vec![
            Expr::Int(1),
            Expr::Error(ErrorKind::UnexpectedText(String::from("two")))
        ]),
        Expr::List(vec![
            Expr::Error(ErrorKind::UnexpectedText(String::from("three"))),
            Expr::Int(4)
        ])
    ]))
);
```

Because we can combine and define recovery strategies as with any other grammar rule in our language, this allows us the liberty to even attempt parsing constructs that don't make sense in our language, as exemplified above with text_recovery. Many modern languages (even Rust!) attempt invalid parses like the above in order to teach new users coming from unfamiliar grammars.

To define your own recovery strategy, Chumsky provides the `recovery::via_parser` utility to be used in conjunction with `Parser::recover_with`.

### Skipping tokens with [`recovery::skip_until`] and [`recovery::skip_then_retry_until`]

Chumsky provides two primitive recovery strategies that can be used in lieu of defining your own:

- [`recovery::skip_until`]: will *skip* input *until* it matches a new construct. It is naive and recommended only as a last resort, as it will result in very poor error generation if abused. TODO what is fallback?

- [`recovery::skip_then_retry_until`]: TODO can't remember where I saw docs for this one before.

## Error Diagnostics
TODO Section on Ariadne?
