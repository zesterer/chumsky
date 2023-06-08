# Why use Parser Combinators

Writing parsers with good error recovery is conceptually difficult and time
consuming. It requires understanding of the parsing algorithm, ontop of which
the recovery strategy has to be built. If you are working on a project who's
syntax is unstable, you may be left in a cycle of painstakingly refactoring the
parser to stay up to date with the changing syntax. Parser combinators are designed
to allow for rapid iteration, making sure that updating the syntax doesn't become
too much of a chore.

For this reason, parser combinators are a great fit for domain-specific languages
for which a parser does not yet exist. Writing a reliable and fault-tolerant
parser can go from a multi-day task to a hour-half task with the help of a good
library.
