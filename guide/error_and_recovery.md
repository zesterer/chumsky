# Error And Recovery

A key property of parsing unstructured data into a more structured, semantic form, is that that unstructured data may not be correctly arranged such that the conversion is possible. While this happens with (basically) any parser, different parsers might have different expectations of how much they want to do to recover from or provide info on malformed data. A high speed assembly interpreter might decide that it just needs to know that something bad happened, while a programming language compiler might want to ponder on the data and its surrounding context and provide as much information as possible to the end user, which might itself involve going over *more* data instead of failing immediately. Certain categories of errors may even be entirely recoverable from!

## What is an [`Error`]?

While Chumsky is responsible for the plumbing and detection of errors based on Parser Combinator outputs, you have full control over the creation, display, contained data and interactions for errors you define. Chumsky achieves this by having parser combinators automatically generate errors based on their parser function's type signature while providing the [`Parser::map_err`] utility to convert the original error type into your own.

It is also entirely possible to rely only on Chumsky's default error types, labelling them with descriptions on [`Parser::map_err`] calls, or letting details emerge from the interplay of the declared parser combinations.

## The Quintessential Quadruplet of Errors

For prototyping and modest use cases, Chumsky provides 4 separate built-in types that implement [`Error`], ranging from a super cheap ZeroSizedType (ZST) to a complex and detailed user-centric error. Instances of these types can be modified to alter their contained data, such as altering the expected value of an expression, the span where the failure ocurred, or by providing an arbitrary context as in [`Rich`].

- [`EmptyErr`]: the ZST defaulted to in most situations, it contains no additional information other than that an error has occurred, but also very minimal overhead. Useful in high performance environments where error recovery may not be viable or performance concerns are more significant than usability concerns.

- [`Cheap`]: contains only [`Span`] information about the associated error, letting you know where it happened, but not giving you much more information besides. As the name implies, it is very cheap, and thus usable for high performance environments where basic usability is still nice to have.

- [`Simple`]: contains the [`Span`], but also the found token at the location of the error. This error is a good middle ground between the raw speed of [`Cheap`] and the detailed user-centric focus of [`Rich`], while still being able to satisfy medium performance requirements.

- [`Rich`]: the recommended type for dealing with user input at the expense of raw speed. Rich is still *fast* for applications like compilers and interpreters, and a great choice if you want to give users a pleasant editing experience first and foremost. Rich error types contain [`Span`] information as well as found and expected values, a [`Label`] to describe the associated parser construction, the ability to merge errors in the same span, as well as a potential [`Context`] with truly arbitrary data.

## The [`Span`] Trait
TODO

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

```
# use chumsky::prelude::*;
# fn parser<'src>() -> impl Parser<'src, &'src str, ()> { end() }
#[test]
fn test_parser() {
    // Our parser expects empty strings, so this should parse successfully
    assert_eq!(parser().parse("").into_result(), Ok(()));

    // Anything other than an empty string should produce an error
    assert!(parser().parse("123").has_errors());
}
```

## Error Handling in Practice
TODO

## Error Diagnostics
TODO Section on Ariadne?