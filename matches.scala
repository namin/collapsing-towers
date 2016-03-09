object Matches {

import Base._
import Lisp._
import Lisp.parser._

val matches_poly_src = """(let matches (lambda matches r (lambda _ s
  (if (equs 'done (car r)) (maybe-lift 'yes)
    (if (equs (maybe-lift 'done) (car s)) (maybe-lift 'no)
      (if (equs (maybe-lift (car r)) (car s)) ((matches (cdr r)) (cdr s)) (maybe-lift 'no))))))
  (lambda _ r (maybe-lift (lambda _ s ((matches r) s)))))
"""


val matches_src = matches_poly_src.replace("maybe-lift", "nolift")
val matchesc_src = matches_poly_src.replace("maybe-lift", "lift")

val Success(matches_val, _) = parseAll(exp, matches_src)
val Success(matchesc_val, _) = parseAll(exp, matchesc_src)

val matches_exp = trans(matches_val, List("arg", "arg2"))
val matchesc_exp = trans(matchesc_val, List("arg", "arg2"))

val matches_exp_anf = reify { anf(List(Sym("XX"), Sym("XX")), matches_exp) }
val matchesc_exp_anf = reify { anf(List(Sym("XX"), Sym("XX")), matchesc_exp) }

val Success(ab_val, _) = parseAll(exp, """(a b done)""")
val Success(ac_val, _) = parseAll(exp, """(a c done)""")

val eval_exp = trans(eval_val,List("arg","arg2", "arg3"))
val evalc_exp = trans(evalc_val,List("arg","arg2", "arg3"))
val eval_exp_anf = reify { anf(List(Sym("XX"),Sym("XX"), Sym("XX")), eval_exp) }
val evalc_exp_anf = reify { anf(List(Sym("XX"),Sym("XX"), Sym("XX")),evalc_exp) }

// Str(yes)
check(evalms(List(matches_val, ab_val, ac_val),App(App(App(App(eval_exp,Var(0)),Sym("nil-env")),Var(1)), Var(1))))("Str(yes)")
// Str(no)
check(evalms(List(matches_val, ab_val, ac_val),App(App(App(App(eval_exp,Var(0)),Sym("nil-env")),Var(1)), Snd(Var(1)))))("Str(no)")
// Str(no)
check(evalms(List(matches_val, ab_val, ac_val),App(App(App(App(eval_exp,Var(0)),Sym("nil-env")),Var(1)), Var(2))))("Str(no)")

// interpretation
check(run { evalms(List(ab_val,matches_val,eval_val), App(App(App(App(eval_exp,Var(1)),Sym("nil-env")),Var(0)),Var(0))) })("Str(yes)")

// double interpretation
check(run { evalms(List(ab_val,matches_val,eval_val), App(App(App(App(App(App(eval_exp,Var(2)),Sym("nil-env")), Var(1)), Sym("nil-env2")), Var(0)), Var(0))) })("Str(yes)")

// generation + interpretation
val c1 = reifyc { evalms(List(ab_val,matches_val,eval_val),App(App(evalc_exp,Var(1)),Sym("nil-env"))) }
println(pretty(c1, Nil))
// Str(yes)
val r1 = run { val m = evalms(Nil,c1); evalms(List(m, ab_val), App(App(Var(0), Var(1)), Var(1))) }
check(r1)("Str(yes)")

// generation + generation + interpretation
val c2 = reifyc { evalms(List(ab_val,matchesc_val,eval_val),App(App(evalc_exp,Var(1)),Sym("nil-env"))) }
val d2 = reifyc { val m = evalms(Nil,c2); evalms(List(m, ab_val), App(Var(0), Var(1))) }
println(pretty(d2, Nil))
val r2 = run { val m = evalms(Nil,d2); evalms(List(m, ab_val), App(Var(0), Var(1))) }
val s2 = run { val m = evalms(Nil,d2); evalms(List(m, ac_val), App(Var(0), Var(1))) }
check(r2)("Str(yes)")
check(s2)("Str(no)")

// interpretation for generation
val c3 = run { evalms(List(ab_val,matchesc_val,eval_val),App(App(eval_exp,Var(1)),Sym("nil-env"))) }
val d3 = reifyc { evalms(List(c3, ab_val), App(Var(0), Var(1))) }
println(pretty(d3, Nil))

// "direct" generation
val d4 = reifyc { evalms(List(ab_val,matchesc_val,eval_val),App(App(App(eval_exp,Var(1)),Sym("nil-env")), Var(0))) }
println(pretty(d4, Nil))

// different interpretation
val matches_ab_poly_src = s"""($matches_poly_src '(a b done))"""
val matches_ab_src = matches_ab_poly_src.replace("maybe-lift", "nolift")
val matchesc_ab_src = matches_ab_poly_src.replace("maybe-lift", "lift")

val Success(matches_ab_val, _) = parseAll(exp, matches_ab_src)
val Success(matchesc_ab_val, _) = parseAll(exp, matchesc_ab_src)

// Str(yes)
val r5 = run { evalms(List(ab_val,matches_ab_val,eval_val),App(App(App(eval_exp,Var(1)),Sym("nil-env")), Var(0))) }

check(r5)("Str(yes)")

val d6 = reifyc { evalms(List(ab_val,matchesc_ab_val,eval_val),App(App(eval_exp,Var(1)),Sym("nil-env"))) }
println(pretty(d6, Nil))

}