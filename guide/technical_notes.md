# Technical Notes

This section contains assorted details about chumsky. Most of this information is irrelevant to beginners, but we
consider it important enough to include for advanced users.

- [Technical Notes](#technical-notes)
- [Classification](#classification)
- [Purity and optimisation](#purity-and-optimisation)

# Classification

Chumsky is a PEG parser by nature. That is to say, it is possible to parse all known context-free grammars with chumsky.
It has not yet been formally proven that PEG parsers can parse _all_ context-free grammars but, for the sake of using
the library, it is reasonable to assume as much.

Chumsky also has limited support for context-sensitive parsing. Chumsky's context-sensitive parsing allows previously
parsed elements of the grammar to inform the parsing of future elements in a limited way.
See [`Parser::ignore_with_ctx`] and [`Parser::then_with_ctx`]for more information.

The term 'PEG++' might be an appropriate description of chumsky, with 'CFG + left context' being a description of the
grammars that it can parse.

Chumsky can also be extended via [`custom`] and [`ExtParser`], permitting it to theoretically parse any parseable
grammar: but this is probably cheating since doing so requires manually implementing such parser logic.

# Purity and optimisation

Chumsky uses a plethora of techniques to improve parser performance. For example, it may skip generating output values
that go unused by the parser (such as the output of `a` in `a.ignore_then(b)`). This also includes combinators like
[`Parser::map`], which accept a user-provided closure. However, chumsky has no control over the behaviour of this
closure, and it's possible to observe the closure being 'optimised away'.

For this reason, unless otherwise specified, any closures/functions used inline within a chumsky parser should be
*semantically* [pure](https://en.wikipedia.org/wiki/Purely_functional_programming): that is, you should not assume that
they are called any specific number of times. This does not mean that they are not permitted to have side effects, but
that those side effects should be irrelevant to the correct functioning of the parser. For example,
[string interning](https://en.wikipedia.org/wiki/String_interning) within [`Parser::map_with`] is an impure operation,
but this impurity does not affect the correct functioning of the parser: interning a string that goes unused can be done
any number of times or not at all without resulting in bad behaviour.
