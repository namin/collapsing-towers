# Collapsing Towers of Interpreters

We are concerned with the following challenge: given a sequence of programming 
languages `L_0,...,L_n` and interpreters for `L_i+1` written in `L_i`, derive 
a compiler from `L_n` to `L_0`. This compiler should be one-pass, and it should be
optimal in the sense that the translation removes all interpretive overhead of the
intermediate languages.

# Pink in Scala

## Code
* __[`base.scala`](base.scala)__ defines the multi-level core language λ↑↓ as a definitional interpreter in Scala.
* __[`lisp.scala`](lisp.scala)__ defines a LISP front end and exercises collapsing on various towers, including the tracing factorial microbenchmark.
* __[`pink.scala`](pink.scala)__ defines meta-circular stage-parametric interpreters for Pink.
* __[`matches.scala`](matches.scala)__ defines matchers on top of the LISP front end.
* __[`bench.scala`](bench.scala)__ defines a generic helper for running microbenchmarks.
