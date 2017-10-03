// Meta-circular stage-parametric interpreter for Pink

import Base._
import Lisp._

object Prog {
  val fac_src = "(lambda f n (if n (* n (f (- n 1))) 1))"
  val fac_val = parseExp(fac_src)
  val fac_exp = trans(fac_val,List("arg"))
  val fac_exp_anf = reify { anf(List(Sym("XX")),fac_exp) }
}
import Prog._

object Pink {

  val ev_poly_src = """
(lambda _ maybe-lift (lambda tie eval (lambda _ exp (lambda _ env
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
    (if (eq?  'run    (car exp))   (run ((eval (cadr exp)) env) ((eval (caddr exp)) env))
    (if (eq?  'log    (car exp))   (log ((eval (cadr exp)) env) ((eval (caddr exp)) env))
    ((env (car exp)) ((eval (cadr exp)) env))))))))))))))))))))))
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

  def test() = {
    testCorrectnessOptimality()
    testInstrumentation()
    testEM()
  }

  def testCorrectnessOptimality() = {
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

    check(pretty(fac_exp_anf, Nil))("""(lambda f0 x1 
  (if x1 
    (let x2 (- x1 1) 
    (let x3 (f0 x2) (* x1 x3))) 
  1))""")
  }

  val evt_poly_src = ev_poly_src.replace("(env exp)", "(if (eq? 'n exp) (log (maybe-lift 0) (env exp)) (env exp))")
  val evtc_src = s"""(lambda eval e ((($evt_poly_src (lambda _ e (lift e))) eval) e))"""
  val evtc_val = parseExp(evtc_src)
  val evtc_exp1 = trans(evtc_val, List("arg1"))
  def testInstrumentation() = {
    // (trace-n-evalc fac-src) ;; => <code of fac with extra log calls >
    val fact_exp = reifyc { evalms(List(fac_val),App(App(evtc_exp1,Var(0)),Sym("nil-env"))) }
    check(pretty(fact_exp, Nil))("""(lambda f0 x1 
  (let x2 (log 0 x1) 
  (if x2 
    (let x3 (log 0 x1) 
    (let x4 (log 0 x1) 
    (let x5 (- x4 1) 
    (let x6 (f0 x5) (* x3 x6))))) 
  1)))
""")

    val oldLog = log
    var s = ""
    log = {x => s += x.toString+";" }
    check(run { evalms(Nil,App(fact_exp,Lit(3))) })("Cst(6)")
    check(s)("Cst(3);Cst(3);Cst(3);Cst(2);Cst(2);Cst(2);Cst(1);Cst(1);Cst(1);Cst(0);")
    log = oldLog
  }

  def addCases(cs: String*): String = {
    val app_case = "((env (car exp)) ((eval (cadr exp)) env))"
    ev_poly_src.replace(app_case, cs.mkString("\n")+"\n"+app_case+(")"*cs.length))
  }

  val ev0_poly_src = addCases(
    "(if (eq? 'EM (car exp)) (run (maybe-lift 0) (trans (car (cdr exp))))")
  val evn_poly_src = addCases(
    "(if (eq? 'EM (car exp)) (let e (car (cdr exp)) (EM ((eval (env 'e)) env)))")

  val ev0_src = s"""(lambda eval e ((($ev0_poly_src (lambda _ e e)) eval) e))"""
  val evn_src = s"""(lambda eval e ((($evn_poly_src (lambda _ e e)) eval) e))"""

  val emt_src = """((EM (((lambda ev exp (lambda _ env
     (if (if (sym? exp) (eq? 'n exp) 0) (log 0 ((eval exp) env)) (((tie ev) exp) env))))
     '(lambda f n (if n (* n (f (- n 1))) 1))) env)) 3)"""
  val ev0_val = parseExp(ev0_src)
  val evn_val = parseExp(evn_src)
  val emt_val = parseExp(emt_src)
  val ev0_exp1 = trans(ev0_val,List("arg"))
  val ev0_exp2 = trans(ev0_val,List("arg", "arg2"))
  def testEM() = {
    // sanity checks
    check(run { evalms(List(fac_val), App(App(App(ev0_exp1, Var(0)), Sym("nil-env")), Lit(4))) })("Cst(24)")
    check(run { evalms(List(fac_val,evn_val), App(App(App(App(App(ev0_exp2,Var(1)),Sym("nil-env")), Var(0)), Sym("nil-env2")), Lit(4))) })("Cst(24)")

    // Section 5.1.2 -- Modifying the Tower Structure
    val oldLog = log
    var s = ""
    log = {x => s += x.toString+";" }
    check(run { evalms(List(emt_val), App(App(ev0_exp1, Var(0)), Sym("nil-env"))) })("Cst(6)")
    check(s)("Cst(3);Cst(3);Cst(3);Cst(2);Cst(2);Cst(2);Cst(1);Cst(1);Cst(1);Cst(0);")
    log = oldLog
  }
}

object Pink_CPS {
  val ev_poly_src = """
(lambda _ maybe-lift (lambda _ eval (lambda _ exp (lambda _ env (lambda _ k
  (if (num?                exp)    (k (maybe-lift exp))
  (if (sym?                exp)    (k (env exp))
  (if (sym?           (car exp))   
    (if (eq?  '+      (car exp))   (((eval (cadr exp)) env) (lambda _ v1 (((eval (caddr exp)) env) (lambda _ v2 (k (+ v1 v2))))))
    (if (eq?  '-      (car exp))   (((eval (cadr exp)) env) (lambda _ v1 (((eval (caddr exp)) env) (lambda _ v2 (k (- v1 v2))))))
    (if (eq?  '*      (car exp))   (((eval (cadr exp)) env) (lambda _ v1 (((eval (caddr exp)) env) (lambda _ v2 (k (* v1 v2))))))
    (if (eq?  'eq?    (car exp))   (((eval (cadr exp)) env) (lambda _ v1 (((eval (caddr exp)) env) (lambda _ v2 (k (eq? v1 v2))))))
    (if (eq?  'if     (car exp))   (((eval (cadr exp)) env) (lambda _ c (if c (((eval (caddr exp)) env) k) (((eval (cadddr exp)) env) k))))
    (if (eq?  'lambda (car exp))        (k (maybe-lift (lambda f x (maybe-lift ((eval (cadddr exp)) 
      (lambda _ y (if (eq? y (cadr exp)) f (if (eq? y (caddr exp)) x (env y)))))))))
    (if (eq?  'let    (car exp))   (((eval (caddr exp)) env) (maybe-lift (lambda _ v (let x v (((eval (cadddr exp)) (lambda _ y (if (eq?  y (cadr exp)) x (env y)))) k)))))
    (if (eq?  'lift   (car exp))   (((eval (cadr exp)) env) (lambda _ v (k (lift v))))
    (if (eq?  'num?   (car exp))   (((eval (cadr exp)) env) (lambda _ v (k (num? v))))
    (if (eq?  'sym?   (car exp))   (((eval (cadr exp)) env) (lambda _ v (k (sym? v))))
    (if (eq?  'car    (car exp))   (((eval (cadr exp)) env) (lambda _ v (k (car v))))
    (if (eq?  'cdr    (car exp))   (((eval (cadr exp)) env) (lambda _ v (k (cdr v))))
    (if (eq?  'cons   (car exp))   (((eval (cadr exp)) env) (lambda _ a (((eval (caddr exp)) env) (lambda _ d (k (maybe-lift (cons a d)))))))
    (if (eq?  'quote  (car exp))   (k (maybe-lift (cadr exp)))
    (((eval (cadr exp)) env) (lambda _ v2 (((env (car exp)) v2) (maybe-lift (lambda _ x (k x))))))))))))))))))))
  (((eval (car exp)) env) (lambda _ v1 (((eval (cadr exp)) env) (lambda _ v2 ((v1 v2) (maybe-lift (lambda _ x (k x))))))))))))))))
"""

  val ev_src = s"""(lambda eval e ((($ev_poly_src (lambda _ e e)) eval) e))"""
  val evc_src = s"""(lambda eval e ((($ev_poly_src (lambda _ e (lift e))) eval) e))"""

  val ev_val = parseExp(ev_src)
  val ev_exp1 = trans(ev_val, List("arg1"))

  val evc_val = parseExp(evc_src)
  val evc_exp1 = trans(evc_val, List("arg1"))

  def test() = {
    // interpretation of fac
    val r1 = run { evalms(List(fac_val), App(App(App(ev_exp1, Var(0)), Sym("nil-env")), Lam(App(App(Var(2),Lit(4)),Lam(Var(4)))))) }
    check(r1)("Cst(24)")

    // compilation of fac
    val facc_exp = reifyc { evalms(List(fac_val),App(App(App(evc_exp1,Var(0)),Sym("nil-env")),Lam(Var(2)))) }
    check(pretty(facc_exp, Nil))("""(lambda f0 x1 
  (lambda f2 x3 
    (if x1 
      (let x4 (- x1 1) 
      (let x5 (f0 x4) 
      (let x6 
        (lambda f6 x7 
          (let x8 (* x1 x7) (x3 x8))) (x5 x6)))) 
    (x3 1))))""")

    val r2 = run { evalms(Nil, App(App(facc_exp, Lit(4)),Lam(Var(1)))) }
    check(r2)("Cst(24)")

    val nested_src = "(lambda f n (if (if n 0 1) 2 3))"
    val nested_val = parseExp(nested_src)
    val r3 = run { evalms(List(nested_val), App(App(App(ev_exp1, Var(0)), Sym("nil-env")), Lam(App(App(Var(2),Lit(0)),Lam(Var(4)))))) }
    check(r3)("Cst(2)")

    val c4 = reifyc { evalms(List(nested_val),App(App(App(evc_exp1,Var(0)),Sym("nil-env")),Lam(Var(2)))) }
    val r4 = run { evalms(Nil, App(App(c4, Lit(0)), Lam(Var(1)))) }
    check(r4)("Cst(2)")

    check(pretty(c4,Nil))("""(lambda f0 x1 
  (lambda f2 x3 
    (if x1 
      (if 0 (x3 2) 
      (x3 3)) 
    
      (if 1 (x3 2) 
      (x3 3)))))""")

  }
}
