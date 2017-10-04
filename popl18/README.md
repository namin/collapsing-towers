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

# Paper ([PDF](http://lampwww.epfl.ch/~amin/drafts/collapsing.pdf))
* __Fig. 1__ corresponds to PLT Redex development in [`core.rkt`](core.rkt).
* __Fig. 2__ is a subset of the Scala development in [`base.scala`](base.scala). The alternative Scheme development is at [`pink-scheme/base.scm`](https://github.com/namin/pink/blob/master/base.scm).
* __Fig. 3__ and other such examples are in the PLT Redex examples in [`core-exs.rkt`](core-exs.rkt).
* Variants of __Fig. 4__ are in [`pink.scala`](pink.scala) and [`pink-scheme/pink.scm`](https://github.com/namin/pink/blob/master/pink.scm).
* Examples of collapsing towers are in [`pink.scala`](pink.scala) and [`pink-scheme/pink-tests.scm`](https://github.com/namin/pink/blob/master/pink-tests.scm), and more crudely in [`lisp.scala`](lisp.scala).
* __Fig. 5__ is developed in [`matches.scala`](matches.scala) and [`pink-scheme/matcher.scm`](https://github.com/namin/pink/blob/master/matcher.scm).
* __Fig. 6__ is derived from examples in [`pink.scala`](pink.scala).
* The Purple examples of Section 7 are collected as [tests](https://github.com/namin/lms-black/tree/master/src/test/scala/lms/black) in [the Purple development](https://github.com/namin/lms-black).
* The Purple development [source](https://github.com/namin/lms-black/tree/master/src/main/scala/lms/black) consists of the stage-polymorphic base interpreter functions ([`eval.scala`](https://github.com/namin/lms-black/blob/master/src/main/scala/lms/black/eval.scala)), the LMS instantiation([`stage.scala`](https://github.com/namin/lms-black/blob/master/src/main/scala/lms/black/stage.scala)), and various utilities including a REPL. The REPL is automatically imported with `sbt console` from the top-level [`purple`](https://github.com/namin/lms-black) directory and can be invoked with `ev`, e.g. `ev("(+ 1 1)")`.
* The benchmarks for Pink are collected in the `benchmarks` method in [`test-main.scala`](test-main.scala). The benchmarks for Purple are collected in [`purple/src/test/.../bench.scala`](https://github.com/namin/lms-black/blob/master/src/test/scala/lms/black/bench.scala) and ran with `sbt test:run` from the the top-level [`purple`](https://github.com/namin/lms-black) directory.
