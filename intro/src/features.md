# Features

* ## std
  *Enabled per default*

  Allows Chumsky to use features of the standard library.

* ## spill-stack
  *Enabled per default*

  Allows deeper recursion by dynamically spilling stack state on to the heap.

* ## nightly
  
  Enable nightly-only features like better compiler diagnostics and a [`Parser`](https://docs.rs/chumsky/latest/chumsky/trait.Parser.html) impl for [`!`](https://doc.rust-lang.org/std/primitive.never.html)

* ## memoization
  
  Allows parser memoisation, speeding up heavily back-tracking parsers and allowing left recursion.

* ## extension
  
  Allows extending chumsky by writing your own parser implementations.

* ## label
  Enable support for parser labelling
  
* ## sync
  Make builtin parsers such as `Boxed` use atomic instead of non-atomic internals.
