# Collapsing Towers of Interpreters

We are concerned with the following challenge: given a sequence of programming 
languages `L_0,...,L_n` and interpreters for `L_i+1` written in `L_i`, derive 
a compiler from `L_n` to `L_0`. This compiler should be one-pass, and it should be
optimal in the sense that the translation removes all interpretive overhead of the
intermediate languages.

# Multi-level core language λ↑↓ in PLT Redex

## Code
* __[`core.rkt`](core.rkt)__ defines the multi-level core language λ↑↓ as a PLT Redex model, using a small-step operational semantics.
* __[`core-exs.rkt`](core.rkt)__ defines some examples to exercise the semantics.

## Run
Run `core-exs.rkt` in [DrRacket](https://racket-lang.org/).

# Pink in Scala

## Code
* __[`base.scala`](base.scala)__ defines the multi-level core language λ↑↓ as a definitional interpreter in Scala.
* __[`lisp.scala`](lisp.scala)__ defines a LISP front end and exercises collapsing on various towers, including the tracing factorial microbenchmark.
* __[`pink.scala`](pink.scala)__ defines meta-circular stage-parametric interpreters for Pink.
* __[`matches.scala`](matches.scala)__ defines matchers on top of the LISP front end.
* __[`bench.scala`](bench.scala)__ defines a generic helper for running microbenchmarks.

## Run
Run `sbt run` using Scala's [SBT](http://www.scala-sbt.org/).

Modify [`test-main.scala`](test-main.scala) to run more or fewer tests and benchmarks.

# Pink in Scheme
available at [namin/pink](https://github.com/namin/pink), here referred to as `pink-scheme`.

# Purple
available at [namin/lms-black](https://github.com/namin/lms-black), here referred to as `purple`.
