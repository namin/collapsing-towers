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
    def checkrun(src: String, dst: String) = {
      val prog_src = s"""(let exec-quote (lambda _ src (exec (trans-quote src))) $src)"""
      val prog_val = parseExp(prog_src)
      val prog_exp = trans(prog_val,Nil)
      val res = reifyv(evalms(Nil,prog_exp))
      check(res)(dst)
    }

    // direct execution
    checkrun(s"""
    (let fac $fac_src 
    (fac 4))""", 
    "Cst(24)")


    // interpretation
    // ((eval fac-src) 4) ;; => 24
    check(run { evalms(List(fac_val), App(App(App(ev_exp1, Var(0)), Sym("nil-env")), Lit(4))) })("Cst(24)")

    checkrun(s"""
    (let eval          (lambda _ e (($ev_src e) 'nil-env))
    (let fac_val       (quote $fac_src)
    (let fac           (eval fac_val)
    (fac 4))))""", 
    "Cst(24)")


    // double interpretation
    // (((eval eval-src) fac-src) 4) ;; => 24
    check(run { evalms(List(fac_val,ev_val), App(App(App(App(App(
      ev_exp2,Var(1)),Sym("nil-env")), Var(0)), Sym("nil-env2")), Lit(4))) })("Cst(24)")

    // triple interpretation
    // ((((eval eval-src) eval-src) fac-src) 4) ;; => 24
    check(run { evalms(List(fac_val,ev_val), App(App(App(App(App(App(App(
      ev_exp2,Var(1)),Sym("nil-env")), Var(1)), Sym("nil-env2")), Var(0)), Sym("nil-env3")), Lit(4))) })("Cst(24)")

    // compilation
    // (evalc fac-src) ;; => <code for fac>
    val c1 = reifyc { evalms(List(fac_val),App(App(evc_exp1,Var(0)),Sym("nil-env"))) }
    check(c1)(fac_exp_anf.toString)
    // ((run 0 (evalc fac-src)) 4) ;; => 24
    check(run { evalms(Nil,App(c1,Lit(4))) })("Cst(24)")

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
  1)))""")

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
    s = ""
    check(run { evalms(List(emt_val, evn_val), App(App(App(App(ev0_exp2, Var(1)), Sym("nil-env")), Var(0)), Sym("nil-env2"))) })("Cst(6)")
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
    check(run { evalms(List(fac_val), App(App(App(ev_exp1, Var(0)), Sym("nil-env")), Lam(App(App(Var(2),Lit(4)),Lam(Var(4)))))) })("Cst(24)")

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

    check(run { evalms(Nil, App(App(facc_exp, Lit(4)),Lam(Var(1)))) })("Cst(24)")

    val nested_src = "(lambda f n (if (if n 0 1) 2 3))"
    val nested_val = parseExp(nested_src)
    check(run { evalms(List(nested_val), App(App(App(
      ev_exp1, Var(0)), Sym("nil-env")), Lam(App(App(Var(2),Lit(0)),Lam(Var(4)))))) })("Cst(2)")

    val c4 = reifyc { evalms(List(nested_val),App(App(App(evc_exp1,Var(0)),Sym("nil-env")),Lam(Var(2)))) }
    check(run { evalms(Nil, App(App(c4, Lit(0)), Lam(Var(1)))) })("Cst(2)")

    check(pretty(c4,Nil))("""(lambda f0 x1 
  (lambda f2 x3 
    (if x1 
      (if 0 (x3 2) 
      (x3 3)) 
    
      (if 1 (x3 2) 
      (x3 3)))))""")

    testEM()
  }

 def addCases(cs: String*): String = {
    val app_case = "(((eval (cadr exp)) env) (lambda _ v2 (((env (car exp)) v2) (maybe-lift (lambda _ x (k x))))))"
    ev_poly_src.replace(app_case, cs.mkString("\n")+"\n"+app_case+(")"*cs.length))
  }

  val ev0_poly_src = addCases(
    "(if (eq? 'EM (car exp)) (run (maybe-lift 0) (trans (car (cdr exp))))")
  val evn_poly_src = addCases(
    "(if (eq? 'EM (car exp)) (let e (car (cdr exp)) (EM ((eval (env 'e)) env)))")

  val ev0_src = s"""(lambda eval e ((($ev0_poly_src (lambda _ e e)) eval) e))"""
  val evn_src = s"""(lambda eval e ((($evn_poly_src (lambda _ e e)) eval) e))"""

  // 5.1.3 Language Extensions in User Code
  // defining call/cc in terms of EM
  val emt_src = """(let call/cc (lambda _ f (EM (
((env 'f) (maybe-lift (lambda _ v (maybe-lift (lambda _ k1 (k1 (k v)))))))
(maybe-lift (lambda _ x x)))))

(+ 3 (call/cc (lambda _ k (k (k (k 1)))))))
"""
  val ev0_val = parseExp(ev0_src)
  val evn_val = parseExp(evn_src)
  val emt_val = parseExp(emt_src)
  val ev0_exp1 = trans(ev0_val,List("arg"))
  val ev0_exp2 = trans(ev0_val,List("arg", "arg2"))
  def testEM() = {
    // sanity check
    check(run { evalms(List(fac_val), App(App(App(ev0_exp1, Var(0)), Sym("nil-env")), Lam(App(App(Var(2),Lit(4)),Lam(Var(4)))))) })("Cst(24)")

    check(run { evalms(List(emt_val), App(App(App(ev0_exp1, Var(0)), Sym("nil-env")), Lam(Var(2)))) })("Cst(10)")
  }
}

// Section 5.2 Compiling under Persistent Semantic Modifications
object Pink_clambda {
  val ev_poly_src = """
(lambda tie eval (lambda _ l (lambda _ exp (lambda _ env
  (if (num?                exp)    ((car l) exp)
  (if (sym?                exp)    (env exp)
  (if (sym?           (car exp))
    (if (eq?  '+      (car exp))   (+   (((eval l) (cadr exp)) env) (((eval l) (caddr exp)) env))
    (if (eq?  '-      (car exp))   (-   (((eval l) (cadr exp)) env) (((eval l) (caddr exp)) env))
    (if (eq?  '*      (car exp))   (*   (((eval l) (cadr exp)) env) (((eval l) (caddr exp)) env))
    (if (eq?  'eq?    (car exp))   (eq? (((eval l) (cadr exp)) env) (((eval l) (caddr exp)) env))
    (if (eq?  'if     (car exp))   (if  (((eval l) (cadr exp)) env) (((eval l) (caddr exp)) env) (((eval l) (cadddr exp)) env))
    (if (if (eq? 'lambda (car exp)) 1 (if (eq? 'clambda (car exp)) (cdr l) 0)) ((car l) (lambda f x (((eval l) (cadddr exp))
      (lambda _ y (if (eq? y (cadr exp)) f (if (eq? y (caddr exp)) x (env y)))))))
    (if (eq? 'clambda (car exp))       (exec 0 (((eval (cons (lambda _ e (lift e)) 1)) (cons 'lambda (cdr exp)))  (lambda _ y (lift-ref (env y)))))
    (if (eq?  'let    (car exp))   (let x (((eval l) (caddr exp)) env) (((eval l) (cadddr exp))
      (lambda _ y (if (eq?  y (cadr exp)) x (env y)))))
    (if (eq?  'lift   (car exp))   (lift (((eval l) (cadr exp)) env))
    (if (eq? 'lift-ref (car exp))  (lift-ref (((eval l) (cadr exp)) env))
    (if (eq?  'num?   (car exp))   (num? (((eval l) (cadr exp)) env))
    (if (eq?  'sym?   (car exp))   (sym? (((eval l) (cadr exp)) env))
    (if (eq?  'pair?  (car exp))   (pair? (((eval l) (cadr exp)) env))
    (if (eq?  'car    (car exp))   (car  (((eval l) (cadr exp)) env))
    (if (eq?  'cdr    (car exp))   (cdr  (((eval l) (cadr exp)) env))
    (if (eq?  'cons   (car exp))   ((car l) (cons (((eval l) (cadr exp)) env) (((eval l) (caddr exp)) env)))
    (if (eq?  'quote  (car exp))   ((car l) (cadr exp))
    (if (eq?  'exec   (car exp))   (exec (((eval l) (cadr exp)) env) (((eval l) (caddr exp)) env))
    (if (eq?  'run    (car exp))   (run (((eval l) (cadr exp)) env) (((eval l) (caddr exp)) env))
    (if (eq?  'log    (car exp))   (log (((eval l) (cadr exp)) env) (((eval l) (caddr exp)) env))
    (if (eq?  'EM     (car exp))   (run ((car l) 0) (trans (car (cdr exp))))
    (if (eq?  'trans (car exp))   (trans (cadr exp))
    ((env (car exp)) (((eval l) (cadr exp)) env))))))))))))))))))))))))
  ((((eval l) (car exp)) env) (((eval l) (cadr exp)) env)))))))))
"""

  val ev_tie_src = s"""(lambda eval l (lambda _ e ((($ev_poly_src eval) l) e)))"""
  val ev_src = s"""($ev_tie_src (cons (lambda _ e e) 0))"""
  val evc_src = s"""($ev_tie_src (cons (lambda _ e (lift e)) 1))"""
  val fc_src = fac_src.replace("lambda", "clambda")
  val fc_val = parseExp(fc_src)

  val ev_val = parseExp(ev_src)
  val ev_exp1 = trans(ev_val, List("arg1"))

  val evc_val = parseExp(evc_src)
  val evc_exp1 = trans(evc_val, List("arg1"))

  def test_clambda() = {
    check(run { evalms(List(fc_val), App(App(App(ev_exp1, Var(0)),Sym("nil-env")),Lit(4))) })("Cst(24)")
    val c1 = (run { evalms(List(fc_val), App(App(ev_exp1, Var(0)),Sym("nil-env"))) }).asInstanceOf[Clo]
    check(c1.env)("List()")
    check(pretty(c1.e, List("r", "n")))("""(if n 
  (let x2 (- n 1) 
  (let x3 (r x2) (* n x3))) 
1)""") // all interpretation overhead is gone

    val c2_val = parseExp("(lambda _ x (clambda _ y (* (+ x x) y)))")
    check(run { evalms(List(c2_val), App(App(App(App(ev_exp1, Var(0)),Sym("nil-env")),Lit(1)),Lit(4))) })("Cst(8)")

    val c3_val = parseExp("(clambda _ x (lambda _ y (* (+ x x) y)))")
    check(run { evalms(List(c3_val), App(App(App(App(ev_exp1, Var(0)),Sym("nil-env")),Lit(1)),Lit(4))) })("Cst(8)")

    val c4_val = parseExp("(clambda _ x (clambda _ y (* (+ x x) y)))")
    check(run { evalms(List(c4_val), App(App(App(App(ev_exp1, Var(0)),Sym("nil-env")),Lit(1)),Lit(4))) })("Cst(8)")

    val c5_val = parseExp("(let inc (lambda _ x (+ x 1)) (clambda _ y (inc y)))")
    check(run { evalms(List(c5_val), App(App(App(ev_exp1, Var(0)),Sym("nil-env")),Lit(4))) })("Cst(5)")

    val c6_val = parseExp("(lambda _ x (clambda _ y (lambda _ l (* (l (+ x x)) (l y)))))")
    check(run { evalms(List(c6_val), App(App(App(App(App(ev_exp1, Var(0)),Sym("nil-env")),Lit(1)),Lit(4)),Lam(Var(2)))) })("Cst(8)")
    val c6 = (run { evalms(List(c6_val), App(App(App(ev_exp1, Var(0)),Sym("nil-env")),Lit(1))) }).asInstanceOf[Clo]
    check(c6.env)("List()")
    check(pretty(c6.e, List("_", "y")))("""(lambda f2 x3 
  (let x4 (+ <special> <special>) 
  (let x5 (x3 x4) 
  (let x6 (x3 y) (* x5 x6)))))""")
    val c7 = reifyc { evalms(List(c6_val), App(App(App(App(App(ev_exp1, Var(0)),Sym("nil-env")),Lit(1)),Lit(4)),Lam(Lift(Var(2))))) }
    check(pretty(c7, Nil))("(* 2 4)")
  }

  def test_em() {
    val oldLog = log
    var s = ""
    log = {x => s += x.toString+";" }

    val ev_log_src = ev_tie_src.replace("(env exp)", "(if (eq? 'n exp) (log ((car l) 0) (env exp)) (env exp))")
    check(run { evalms(List(parseExp(s"(EM ((($ev_log_src l) '($fac_src 4)) env))")),
      App(App(ev_exp1, Var(0)), Sym("nil-env"))) })("Cst(24)")
    check(s)("Cst(4);Cst(4);Cst(4);Cst(3);Cst(3);Cst(3);Cst(2);Cst(2);Cst(2);Cst(1);Cst(1);Cst(1);Cst(0);")
    s = ""

    check(run { evalms(List(parseExp(s"(EM ((($ev_log_src l) '(${fac_src.replace("lambda", "clambda")} 4)) env))")),
      App(App(ev_exp1, Var(0)), Sym("nil-env"))) })("Cst(24)")
    check(s)("Cst(4);Cst(4);Cst(4);Cst(3);Cst(3);Cst(3);Cst(2);Cst(2);Cst(2);Cst(1);Cst(1);Cst(1);Cst(0);")
    s = ""

    check(run { evalms(List(parseExp(s"""(EM ((((lambda ev l (lambda _ exp (lambda _ env
    (if (if (sym? exp) (eq? 'n exp) 0) (log ((car l) 0) (((eval l) exp) env))
    ((((tie ev) l) exp) env))))) l) '($fac_src 4)) env))""")), App(App(ev_exp1, Var(0)), Sym("nil-env"))) })("Cst(24)")
    check(s)("Cst(4);Cst(4);Cst(4);Cst(3);Cst(3);Cst(3);Cst(2);Cst(2);Cst(2);Cst(1);Cst(1);Cst(1);Cst(0);")
    s = ""

    check(run { evalms(List(parseExp(s"""(EM ((((lambda ev l (lambda _ exp (lambda _ env
    (if (if (sym? exp) (eq? 'n exp) 0) (log ((car l) 0) (((eval l) exp) env))
    ((((tie ev) l) exp) env))))) l) '(${fac_src.replace("lambda", "clambda")} 4)) env))""")), App(App(ev_exp1, Var(0)), Sym("nil-env"))) })("Cst(24)")
    check(s)("Cst(4);Cst(4);Cst(4);Cst(3);Cst(3);Cst(3);Cst(2);Cst(2);Cst(2);Cst(1);Cst(1);Cst(1);Cst(0);")
    s = ""

    log = oldLog
  }

  def test() = {
    test_clambda()
    test_em()
  }
}
