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

val Success(ab_val, _) = parseAll(exp, """(a b done)""")
val Success(ac_val, _) = parseAll(exp, """(a c done)""")

val eval_exp = trans(eval_val,List("arg","arg2", "arg3"))
val evalc_exp = trans(evalc_val,List("arg","arg2", "arg3"))

val matches_ab_poly_src = s"""($matches_poly_src '(a b done))"""
val matches_ab_src = matches_ab_poly_src.replace("maybe-lift", "nolift")
val matchesc_ab_src = matches_ab_poly_src.replace("maybe-lift", "lift")

val Success(matches_ab_val, _) = parseAll(exp, matches_ab_src)
val Success(matchesc_ab_val, _) = parseAll(exp, matchesc_ab_src)

val matches_bis_src = """
(let match_loop (lambda match_loop m (lambda _ s
  (if (equs 'yes (m s))
      'yes
      (if (equs 'done (car s))
          'no
         ((match_loop m) (cdr s))))))
(let star_loop (lambda star_loop m (lambda _ c (lambda _ s
  (if (equs 'yes (m s))
      'yes
      (if (equs 'done (car s))
          'no
          (if (equs '_ c)
              (((star_loop m) c) (cdr s))
              (if (equs c (car s))
                 (((star_loop m) c) (cdr s))
                 'no)))))))
(let match_here (lambda match_here r
  (if (equs 'done (car r)) (lambda _ s 'yes)
  (let m (if (equs '_ (car r))
               (lambda _ s (if (equs 'done (car s)) 'no ((match_here (cdr r)) (cdr s))))
               (lambda _ s (if (equs 'done (car s)) 'no
                          (if (equs (car r) (car s))
                              ((match_here (cdr r)) (cdr s))
                              'no))))
    (if (equs 'done (car (cdr r)))
        (if (equs '$ (car r))
            (lambda _ s (if (equs 'done (car s)) 'yes 'no))
            m)
    (if (equs '* (car (cdr r)))
        ((star_loop (match_here (cdr (cdr r)))) (car r))
        m)))))
(let match (lambda match r
  (if (equs 'done (car r)) (lambda _ s 'yes)
      (if (equs '^ (car r))
          (match_here (cdr r))
          (match_loop (match_here r)))))
match))))
"""

val Success(matches_bis_val, _) = parseAll(exp, matches_bis_src)

val Success(a__val, _) = parseAll(exp, """(^ a _ $ done)""")

val Success(a__star_a_val, _) = parseAll(exp, """(a _ * a done)""")

val Success(a_bstar_a_val, _) = parseAll(exp, """(a b * a done)""")

val Success(abba_val, _) = parseAll(exp, """(a b b a done)""")

val Success(abca_val, _) = parseAll(exp, """(a b c a done)""")

def testMatchesBis() = {
  println("// ------- test matches bis --------")
  def test1(re: Val, s: Val, e: Boolean) = {
    check(evalms(List(matches_bis_val, re, s),
      App(App(App(App(eval_exp,Var(0)),Sym("nil-env")),Var(1)), Var(2))
    ))(if (e) "Str(yes)" else "Str(no)")
  }
  test1(ab_val, ab_val, true)
  test1(ab_val, ac_val, false)
  test1(ab_val, abba_val, true)
  test1(a__val, ab_val, true)
  test1(a__val, ac_val, true)
  test1(a__val, abba_val, false)
  test1(a_bstar_a_val, abba_val, true)
  test1(a_bstar_a_val, abca_val, false)
  test1(a__star_a_val, abba_val, true)
  test1(a__star_a_val, abca_val, true)
}

def testMatches() = {
println("// ------- test matches --------")
check(evalms(List(matches_val, ab_val, ac_val),App(App(App(App(eval_exp,Var(0)),Sym("nil-env")),Var(1)), Var(1))))("Str(yes)")
check(evalms(List(matches_val, ab_val, ac_val),App(App(App(App(eval_exp,Var(0)),Sym("nil-env")),Var(1)), Snd(Var(1)))))("Str(no)")
check(evalms(List(matches_val, ab_val, ac_val),App(App(App(App(eval_exp,Var(0)),Sym("nil-env")),Var(1)), Var(2))))("Str(no)")

// interpretation
check(run { evalms(List(ab_val,matches_val,eval_val), App(App(App(App(eval_exp,Var(1)),Sym("nil-env")),Var(0)),Var(0))) })("Str(yes)")

// double interpretation
check(run { evalms(List(ab_val,matches_val,eval_val), App(App(App(App(App(App(eval_exp,Var(2)),Sym("nil-env")), Var(1)), Sym("nil-env2")), Var(0)), Var(0))) })("Str(yes)")

// generation + interpretation
val c1 = reifyc { evalms(List(ab_val,matches_val,eval_val),App(App(evalc_exp,Var(1)),Sym("nil-env"))) }
//println(pretty(c1, Nil))
val r1 = run { val m = evalms(Nil,c1); evalms(List(m, ab_val), App(App(Var(0), Var(1)), Var(1))) }
check(r1)("Str(yes)")

// generation + generation + interpretation
val c2 = reifyc { evalms(List(ab_val,matchesc_val,eval_val),App(App(evalc_exp,Var(1)),Sym("nil-env"))) }
val d2 = reifyc { val m = evalms(Nil,c2); evalms(List(m, ab_val), App(Var(0), Var(1))) }
println(pretty(d2, Nil))
val expected = pretty(d2, Nil).toString
val r2 = run { val m = evalms(Nil,d2); evalms(List(m, ab_val), App(Var(0), Var(1))) }
val s2 = run { val m = evalms(Nil,d2); evalms(List(m, ac_val), App(Var(0), Var(1))) }
check(r2)("Str(yes)")
check(s2)("Str(no)")

// interpretation for generation
val c3 = run { evalms(List(ab_val,matchesc_val,eval_val),App(App(eval_exp,Var(1)),Sym("nil-env"))) }
val d3 = reifyc { evalms(List(c3, ab_val), App(Var(0), Var(1))) }
check(pretty(d3, Nil))(expected)

// "direct" generation
val d4 = reifyc { evalms(List(ab_val,matchesc_val,eval_val),App(App(App(eval_exp,Var(1)),Sym("nil-env")), Var(0))) }
check(pretty(d4, Nil))(expected)

// different interpretation
val r5 = run { evalms(List(ab_val,matches_ab_val,eval_val),App(App(App(eval_exp,Var(1)),Sym("nil-env")), Var(0))) }
check(r5)("Str(yes)")

val d6 = reifyc { evalms(List(ab_val,matchesc_ab_val,eval_val),App(App(eval_exp,Var(1)),Sym("nil-env"))) }
check(pretty(d6, Nil))(expected)
}
}
