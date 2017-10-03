// Meta-circular stage-parametric interpreter for Pink

import Base._
import Lisp._

object Pink {

  val ev_poly_src = """
(lambda _ maybe-lift (lambda _ eval (lambda _ exp (lambda _ env
  (if (num?                exp)    (maybe-lift exp)
  (if (sym?                exp)    (env exp)
  (if (sym?           (car exp))   
    (if (eq?  '+      (car exp))   (+   ((eval (cadr exp)) env) ((eval (caddr exp)) env))
    (if (eq?  '-      (car exp))   (-   ((eval (cadr exp)) env) ((eval (caddr exp)) env))
    (if (eq?  '*      (car exp))   (*   ((eval (cadr exp)) env) ((eval (caddr exp)) env))
    (if (eq?  'eq?    (car exp))   (eq? ((eval (cadr exp)) env) ((eval (caddr exp)) env))
    (if (eq?  'if     (car exp))   (if  ((eval (cadr exp)) env) ((eval (caddr exp)) env) ((eval (cadddr exp)) env))
    (if (eq?  'lambda (car exp))   (maybe-lift (lambda f x ((eval (cadddr exp)) 
      (lambda _ y (if (eq? y (cadr exp)) f (if (eq? y (caddr exp)) x (env y)))))))
    (if (eq?  'let    (car exp))   (let x ((eval (caddr exp)) env) ((eval (cadddr exp))
      (lambda _ y (if (eq?  y (cadr exp)) x (env y)))))
    (if (eq?  'lift   (car exp))   (lift ((eval (cadr exp)) env))
    (if (eq?  'num?   (car exp))   (num? ((eval (cadr exp)) env))
    (if (eq?  'sym?   (car exp))   (sym? ((eval (cadr exp)) env))
    (if (eq?  'car    (car exp))   (car  ((eval (cadr exp)) env))
    (if (eq?  'cdr    (car exp))   (cdr  ((eval (cadr exp)) env))
    (if (eq?  'cadr   (car exp))   (cadr  ((eval (cadr exp)) env))
    (if (eq?  'caddr  (car exp))   (caddr  ((eval (cadr exp)) env))
    (if (eq?  'cadddr (car exp))   (cadddr  ((eval (cadr exp)) env))
    (if (eq?  'cons   (car exp))   (maybe-lift (cons ((eval (cadr exp)) env) ((eval (caddr exp)) env)))
    (if (eq?  'quote  (car exp))   (maybe-lift (cadr exp))
    (if (eq?  'pair?  (car exp))   (pair? ((eval (cadr exp)) env))
    ((env (car exp)) ((eval (cadr exp)) env))))))))))))))))))))
  (((eval (car exp)) env) ((eval (cadr exp)) env)))))))))
"""

  val ev_src = s"""(lambda eval e ((($ev_poly_src (lambda _ e e)) eval) e))"""
  val evc_src = s"""(lambda eval e ((($ev_poly_src (lambda _ e (lift e))) eval) e))"""

  val ev_val = parseExp(ev_src)
  val ev_exp1 = trans(ev_val, List("arg1"))
  val ev_exp2 = trans(ev_val, List("arg1", "arg2"))
  val ev_exp3 = trans(ev_val, List("arg1", "arg2", "arg3"))
  val ev_exp_anf = reify { anf(List(Sym("XX")),ev_exp1) }

  val evc_val = parseExp(evc_src)
  val evc_exp1 = trans(evc_val, List("arg1"))
  val evc_exp_anf = reify { anf(List(Sym("XX")),evc_exp1) }

  val fac_src = "(lambda f n (if n (* n (f (- n 1))) 1))"
  val fac_val = parseExp(fac_src)
  val fac_exp = trans(fac_val,List("arg"))
  val fac_exp_anf = reify { anf(List(Sym("XX")),fac_exp) }

  def test() = {
    // Correctness and Optimality

    // interpretation
    // ((eval fac-src) 4) ;; => 24
    val i1 = run { evalms(List(fac_val), App(App(App(ev_exp1, Var(0)), Sym("nil-env")), Lit(4))) }
    check(i1)("Cst(24)")

    // double interpretation
    // (((eval eval-src) fac-src) 4) ;; => 24
    val i2 = run { evalms(List(fac_val,ev_val), App(App(App(App(App(ev_exp2,Var(1)),Sym("nil-env")), Var(0)), Sym("nil-env2")), Lit(4))) }
    check(i2)("Cst(24)")

    // triple interpretation
    // ((((eval eval-src) eval-src) fac-src) 4) ;; => 24
    val i3 = run { evalms(List(fac_val,ev_val), App(App(App(App(App(App(App(ev_exp2,Var(1)),Sym("nil-env")), Var(1)), Sym("nil-env2")), Var(0)), Sym("nil-env3")), Lit(4))) }
    check(i3)("Cst(24)")

    // compilation
    // (evalc fac-src) ;; => <code for fac>
    val c1 = reifyc { evalms(List(fac_val),App(App(evc_exp1,Var(0)),Sym("nil-env"))) }
    check(c1)(fac_exp_anf.toString)
    // ((run 0 (evalc fac-src)) 4) ;; => 24
    val r1 = run { evalms(Nil,App(c1,Lit(4))) }
    check(r1)("Cst(24)")

    // optimality: verify collapse
    // ((eval evalc-src) fac-src) ;; => <code for fac>
    check(reifyc { evalms(List(fac_val,evc_val), App(App(App(App(ev_exp2,Var(1)),Sym("nil-env")), Var(0)), Sym("nil-env2"))) })(fac_exp_anf.toString)
    // ((eval evalc-src) eval-src) ;; => <code for eval>
    check(reifyc { evalms(List(ev_val,evc_val), App(App(App(App(ev_exp2,Var(1)),Sym("nil-env")), Var(0)), Sym("nil-env2"))) })(ev_exp_anf.toString)
    // ((eval evalc-src) evalc-src) ;; => <code for eval>
    check(reifyc { evalms(List(evc_val,evc_val), App(App(App(App(ev_exp2,Var(1)),Sym("nil-env")), Var(0)), Sym("nil-env2"))) })(evc_exp_anf.toString)
    // further tower
    // (((eval eval-src) evalc-src) fac-src) ;; => <code for fac>
    check(reifyc { evalms(List(fac_val,evc_val, ev_val), App(App(App(App(App(App(ev_exp3,Var(2)), Sym("nil-env0")), Var(1)),Sym("nil-env")), Var(0)), Sym("nil-env2"))) })(fac_exp_anf.toString)
  }
}
