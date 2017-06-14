object Pink {
  import Base._
  import Lisp._

  val ev_poly_src = """
(lambda _ eval (lambda _ l (lambda _ exp (lambda _ env
  (if (num?                exp)    (l exp)
  (if (sym?                exp)    (env exp)
  (if (sym?           (car exp))   
    (if (eq?  '+      (car exp))   (+   (((eval l) (cadr exp)) env) (((eval l) (caddr exp)) env))
    (if (eq?  '-      (car exp))   (-   (((eval l) (cadr exp)) env) (((eval l) (caddr exp)) env))
    (if (eq?  '*      (car exp))   (*   (((eval l) (cadr exp)) env) (((eval l) (caddr exp)) env))
    (if (eq?  'eq?    (car exp))   (eq? (((eval l) (cadr exp)) env) (((eval l) (caddr exp)) env))
    (if (eq?  'if     (car exp))   (if  (((eval l) (cadr exp)) env) (((eval l) (caddr exp)) env) (((eval l) (cadddr exp)) env))
    (if (eq?  'lambda (car exp))        (l (lambda f x (((eval l) (cadddr exp))
      (lambda _ y (if (eq? y (cadr exp)) f (if (eq? y (caddr exp)) x (env y)))))))
    (if (eq?  'clambda (car exp))       ((lambda _ e (lift e)) (lambda f x (((eval (lambda _ e (lift e))) (cadddr exp))
      (lambda _ y (if (eq? y (cadr exp)) f (if (eq? y (caddr exp)) x (env y)))))))
    (if (eq?  'let    (car exp))   (let x (((eval l) (caddr exp)) env) (((eval l) (cadddr exp))
      (lambda _ y (if (eq?  y (cadr exp)) x (env y)))))
    (if (eq?  'lift   (car exp))   (lift (((eval l) (cadr exp)) env))
    (if (eq?  'num?   (car exp))   (num? (((eval l) (cadr exp)) env))
    (if (eq?  'sym?   (car exp))   (sym? (((eval l) (cadr exp)) env))
    (if (eq?  'car    (car exp))   (car  (((eval l) (cadr exp)) env))
    (if (eq?  'cdr    (car exp))   (cdr  (((eval l) (cadr exp)) env))
    (if (eq?  'cons   (car exp))   (l (cons (((eval l) (cadr exp)) env) (((eval l) (caddr exp)) env)))
    (if (eq?  'quote  (car exp))   (l (cadr exp))
    ((env (car exp)) (((eval l) (cadr exp)) env)))))))))))))))))
  ((((eval l) (car exp)) env) (((eval l) (cadr exp)) env)))))))))
""".
    replace("num?", "isNum").
    replace("sym?", "isStr").
    replace("eq?", "equs").
    replace("(cadr exp)","(car (cdr exp))").
    replace("(caddr exp)","(car (cdr (cdr exp)))").
    replace("(cadddr exp)","(car (cdr (cdr (cdr exp))))")

  val ev_tie_src = s"""(lambda eval l (lambda _ e ((($ev_poly_src eval) l) e)))"""
  val ev_src = s"""($ev_tie_src (lambda _ e e))"""
  val ev_val = parseExp(ev_src)
  val ev_exp1 = trans(ev_val, List("arg1"))
  val evc_src = s"""($ev_tie_src (lambda _ e (lift e)))"""
  val evc_val = parseExp(evc_src)
  val evc_exp1 = trans(evc_val, List("arg1"))

  def testPink() = {
    println("Pink tests")
    val r1 = run { evalms(List(fac_val), App(App(App(ev_exp1, Var(0)), Sym("nil-env")), Lit(4))) }
    check(r1)("Cst(24)")

    val c1 = reifyc { evalms(List(fac_val),App(App(evc_exp1,Var(0)),Sym("nil-env"))) }
    check(c1)(fac_exp_anf.toString)
    val r2 = run { evalms(Nil,App(c1,Lit(4))) }
    check(r2)("Cst(24)")

    // Note:
    // Is this what we want for clambda? I'd expect something more fluid,
    // where compilation happens but then we can run it back in.
    val fc_val = parseExp(fac_src.replace("lambda", "clambda"))
    val c2 = reifyc { evalms(List(fc_val),App(App(ev_exp1, Var(0)), Sym("nil-env"))) }
    check(c2)(fac_exp_anf.toString)
    val r3 = run { evalms(Nil,App(c2,Lit(4))) }
    check(r3)("Cst(24)")
  }
}
