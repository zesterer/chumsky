# Conclusion

Here ends our exploration into Chumsky's API. We only scratched the surface of what Chumsky can do, but now you'll need
to rely on the examples in the repository and the API doc examples for further help. Nonetheless, I hope it was an
interesting foray into the use of parser combinators for the development of parsers.

If nothing else, you've now got a neat little calculator language to play with.

Interestingly, there is a subtle bug in Foo's `eval` function that produces unexpected scoping behaviour with function
calls. I'll leave finding it as an exercise for the reader.

## Homework
<hr>

- Find the interesting function scoping bug and consider how it could be fixed

- Split token lexing into a separate compilation stage to avoid the need for `.padded()` in the parser

- Add more operators

- Add an `if <expr> then <expr> else <expr>` ternary operator

- Add values of different types by turning `f64` into an `enum`

- Add lambdas to the language

- Format the error message in a more useful way, perhaps by providing a reference to the original code