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
* __[`lisp.scala`](lisp.scala)__ defines a LISP front end.
* __[`pink.scala`](pink.scala)__ defines meta-circular stage-parametric interpreters for Pink.
* __[`matcher.scala`](matcher.scala)__ defines a regular expression matcher on top of LISP front end & Pink.
* __[`bench.scala`](bench.scala)__ defines a microbenchmark for comparing evaluation and compilation in Pink.

## Run
Run `sbt run` using Scala's [SBT](http://www.scala-sbt.org/).

Modify [`test-main.scala`](test-main.scala) to run more or fewer tests and benchmarks.

# Pink in Scheme
available at [namin/pink](https://github.com/namin/pink), here referred to as `pink-scheme`.

# Purple
available at [namin/lms-black](https://github.com/namin/lms-black), here referred to as `purple`.

# Paper ([PDF](http://lampwww.epfl.ch/~amin/drafts/collapsing.pdf))
## 3 Multi-Level Core Language λ↑↓
* __Fig. 1__ corresponds to PLT Redex development in [`core.rkt`](core.rkt).
* __Fig. 2__ is a subset of the Scala development in [`base.scala`](base.scala). The alternative Scheme development is at [`pink-scheme/base.scm`](https://github.com/namin/pink/blob/master/base.scm).
* __Fig. 3__ and other such examples are in the PLT Redex examples in [`core-exs.rkt`](core-exs.rkt).
### 3.1 A Lisp-Like Front-End
* This section uses Scheme syntax for illustration. The more extensive matcher is developed in [`matcher.scala`](matcher.scala).
### 3.2 Stage Polymorphism
* Again the specific example used here in Scheme syntax is for illustration, but the technique of abstracting over the stage with via η-expansion is used extensively, for example in [`pink.scala`](pink.scala).
## 4 Building and Collapsing Towers
* Variants of __Fig. 4__ are in [`pink.scala`](pink.scala) and [`pink-scheme/pink.scm`](https://github.com/namin/pink/blob/master/pink.scm).
* Examples of collapsing towers are in [`pink.scala`](pink.scala) and [`pink-scheme/pink-tests.scm`](https://github.com/namin/pink/blob/master/pink-tests.scm).
* __Fig. 5__ is developed in [`matcher.scala`](matcher.scala) and [`pink-scheme/matcher.scm`](https://github.com/namin/pink/blob/master/matcher.scm).
* __Fig. 6__ is derived from examples in [`pink.scala`](pink.scala).
### 4.1 Correctness and Optimality
* The `testCorrectnessOptimality()` method in [`pink.scala`](pink.scala) directly follows the examples in this section.
### 4.2 Deriving Translators from Heterogeneous Towers
#### 4.2.1 Instrumenting Execution
* The `testInstrumentation()` method in [`pink.scala`](pink.scala) demonstrates the example of this section.
* The further tests deriving translators in [`matcher.scala`](matcher.scala) demonstrates how translators and translator generators can be derived.
#### 4.2.2 CPS Transform
* The object `Pink_CPS` in [`pink.scala`](pink.scala) shows a range of CPS-related transformations.
## 5 Towards Reflective Towers
### 5.1 Execute-at-Metalevel
#### 5.1.2 Modifying the Tower Structure
* The `testEM()` method in the object `Pink` in [`pink.scala`](pink.scala) demonstrates the example of this section.
#### 5.1.3 Language Extensions in User Code
* The `testEM()` method in the object `Pink_CPS` in [`pink.scala`](pink.scala) demonstrates the example of this section.
### 5.2 Compiling under Persistent Semantic Modifications
* The object `Pink_clambda`  in [`pink.scala`](pink.scala) shows how to implement and exercise `clambda` in Pink.
## Section 6 and beyond
* The Purple examples of Section 7 are collected as [tests](https://github.com/namin/lms-black/tree/master/src/test/scala/lms/black) in [the Purple development](https://github.com/namin/lms-black).
* The Purple development [source](https://github.com/namin/lms-black/tree/master/src/main/scala/lms/black) consists of the stage-polymorphic base interpreter functions ([`eval.scala`](https://github.com/namin/lms-black/blob/master/src/main/scala/lms/black/eval.scala)), the LMS instantiation([`stage.scala`](https://github.com/namin/lms-black/blob/master/src/main/scala/lms/black/stage.scala)), and various utilities including a REPL. The REPL is automatically imported with `sbt console` from the top-level [`purple`](https://github.com/namin/lms-black) directory and can be invoked with `ev`, e.g. `ev("(+ 1 1)")`.
* The benchmarks for Pink are collected in [`bench.scala`](bench.scala). The benchmarks for Purple are collected in [`purple/src/test/.../bench.scala`](https://github.com/namin/lms-black/blob/master/src/test/scala/lms/black/bench.scala) and ran with `sbt test:run` from the the top-level [`purple`](https://github.com/namin/lms-black) directory.
