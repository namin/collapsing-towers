// Meta-circular stage-parametric interpreter for Pink

import Base._
import Lisp._

object PinkBase {
  val fac_src = "(lambda f n (if (eq? n 0) 1 (* n (f (- n 1)))))"
  val fac_val = parseExp(fac_src)
  val fac_exp = trans(fac_val,List("arg"))
  val fac_exp_anf = reify { anf(List(Sym("XX")),fac_exp) }
  def ev_nolift(src: String) = s"(lambda eval e ((($src (lambda _ e e)) eval) e))"
  def ev_lift(src: String) = s"(lambda eval e ((($src (lambda _ e (lift e))) eval) e))"
  def ev_nil(src: String) = s"(lambda _ e (($src e) 'nil-env))"
}
import PinkBase._

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
  val eval_src = ev_nil(ev_nolift(ev_poly_src))
  val evalc_src = ev_nil(ev_lift(ev_poly_src))

  val eval_val = parseExp(eval_src)
  val eval_exp1 = trans(eval_val, List("arg1"))
  val eval_exp_anf = reify { anf(List(Sym("XX")),eval_exp1) }

  val evalc_val = parseExp(evalc_src)
  val evalc_exp1 = trans(evalc_val, List("arg1"))
  val evalc_exp_anf = reify { anf(List(Sym("XX")),evalc_exp1) }

  def test() = {
    println("// ------- Pink.test --------")
    testCorrectnessOptimality()
    testInstrumentation()
    testEM()
  }

  def testCorrectnessOptimality() = {
    println("Correctness and optimality...")
    // direct execution
    checkrun(s"""
    (let fac $fac_src 
    (fac 4))""",
    "Cst(24)")

    // interpretation
    checkrun(s"""
    (let eval          $eval_src
    (let fac_src       (quote $fac_src)

    ((eval fac_src) 4)))""",
    "Cst(24)")

    // double interpretation
    checkrun(s"""
    (let eval          $eval_src
    (let fac_src       (quote $fac_src)
    (let eval_src      (quote $eval_src)

    (((eval eval_src) fac_src) 4))))""",
    "Cst(24)")

    // triple interpretation
    checkrun(s"""
    (let eval          $eval_src
    (let fac_src       (quote $fac_src)
    (let eval_src      (quote $eval_src)

    ((((eval eval_src) eval_src) fac_src) 4))))""",
    "Cst(24)")

    // compilation
    checkcode(s"""
    (let evalc         $evalc_src
    (let fac_src       (quote $fac_src)

    (evalc fac_src)))""",
    prettycode(fac_exp_anf))

    checkrun(s"""
    (let evalc         $evalc_src
    (let fac_src       (quote $fac_src)

    ((run 0 (evalc fac_src)) 4)))""",
    "Cst(24)")

    // optimality: verify collapse
    checkcode(s"""
    (let eval          $eval_src
    (let evalc_src     (quote $evalc_src)
    (let fac_src       (quote $fac_src)

    ((eval evalc_src) fac_src))))""",
    prettycode(fac_exp_anf))

    checkcode(s"""
    (let eval          $eval_src
    (let evalc_src     (quote $evalc_src)
    (let eval_src      (quote $eval_src)

    ((eval evalc_src) eval_src))))""",
    prettycode(eval_exp_anf))

    checkcode(s"""
    (let eval          $eval_src
    (let evalc_src     (quote $evalc_src)

    ((eval evalc_src) evalc_src)))""",
    prettycode(evalc_exp_anf))

    // further tower
    checkcode(s"""
    (let eval          $eval_src
    (let eval_src      (quote $eval_src)
    (let evalc_src     (quote $evalc_src)
    (let fac_src       (quote $fac_src)

    (((eval eval_src) evalc_src) fac_src)))))""",
    prettycode(fac_exp_anf))

    // confirming Figure 7 (left)
    check(prettycode(fac_exp_anf))("""(lambda f0 x1 
  (let x2 (eq? x1 0) 
  (if x2 1 
  
    (let x3 (- x1 1) 
    (let x4 (f0 x3) (* x1 x4))))))""")

    testDone()
  }

  val evt_poly_src = ev_poly_src.replace("(env exp)", "(if (eq? 'n exp) (log (maybe-lift 0) (env exp)) (env exp))")
  val trace_n_evalc_src = ev_nil(ev_lift(evt_poly_src))

  def testInstrumentation() = {
    println("Instrumentation...")

    checkcode(s"""
    (let trace_n_evalc $trace_n_evalc_src
    (let fac_src       (quote $fac_src)

    (trace_n_evalc fac_src)))""",
    // confirming Figure 7 (middle)
    """(lambda f0 x1 
  (let x2 (log 0 x1) 
  (let x3 (eq? x2 0) 
  (if x3 1 
  
    (let x4 (log 0 x1) 
    (let x5 (log 0 x1) 
    (let x6 (- x5 1) 
    (let x7 (f0 x6) (* x4 x7)))))))))""")

    checkrunlog(s"""
    (let trace_n_evalc $trace_n_evalc_src
    (let fac_src       (quote $fac_src)

    ((run 0 (trace_n_evalc fac_src)) 3)))""",
    "Cst(6)",
    "Cst(3);Cst(3);Cst(3);Cst(2);Cst(2);Cst(2);Cst(1);Cst(1);Cst(1);Cst(0);")

    testDone()
  }

  def addCases(cs: String*): String = {
    val app_case = "((env (car exp)) ((eval (cadr exp)) env))"
    ev_poly_src.replace(app_case, cs.mkString("\n")+"\n"+app_case+(")"*cs.length))
  }

  val ev0_poly_src = addCases(
    "(if (eq? 'EM (car exp)) (run (maybe-lift 0) (trans (car (cdr exp))))")
  val evn_poly_src = addCases(
    "(if (eq? 'EM (car exp)) (let e (car (cdr exp)) (EM ((eval (env 'e)) env)))")

  val eval0_src = ev_nil(ev_nolift(ev0_poly_src))
  val evaln_src = ev_nil(ev_nolift(evn_poly_src))

  val emt_src = """((EM (((lambda ev exp (lambda _ env
     (if (if (sym? exp) (eq? 'n exp) 0) (log 0 ((eval exp) env)) (((tie ev) exp) env))))
     '(lambda f n (if n (* n (f (- n 1))) 1))) env)) 3)"""

  def testEM() = {
    println("EM...")

    // sanity checks
    checkrun(s"""
    (let eval0     $eval0_src
    (let fac_src   (quote $fac_src)
    ((eval0 fac_src) 4)))""", "Cst(24)")
    checkrun(s"""
    (let eval0     $eval0_src
    (let evaln_src (quote $evaln_src)
    (let fac_src   (quote $fac_src)
    (((eval0 evaln_src) fac_src) 4))))""", "Cst(24)")

    // Section 5.1.2 -- Modifying the Tower Structure
    checkrunlog(s"""
    (let eval0     $eval0_src
    (let emt_src   (quote $emt_src)
    (eval0 emt_src)))""", "Cst(6)",
    "Cst(3);Cst(3);Cst(3);Cst(2);Cst(2);Cst(2);Cst(1);Cst(1);Cst(1);Cst(0);")

    checkrunlog(s"""
    (let eval0     $eval0_src
    (let evaln_src (quote $evaln_src)
    (let emt_src   (quote $emt_src)
    ((eval0 evaln_src) emt_src))))""", "Cst(6)",
    "Cst(3);Cst(3);Cst(3);Cst(2);Cst(2);Cst(2);Cst(1);Cst(1);Cst(1);Cst(0);")

    testDone()
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

  val eval_src = ev_nil(ev_nolift(ev_poly_src))
  val evalc_src = ev_nil(ev_lift(ev_poly_src))

  def test() = {
    println("// ------- Pink_CPS.test --------")

    testBasics()
    testEM()
  }

  def testBasics() {
    println("Basics...")

    // interpretation of fac
    checkrun(s"""
    (let eval    $eval_src
    (let fac_src (quote $fac_src)
    ((eval fac_src) (lambda _ f ((f 4) (lambda _ x x))))))""", "Cst(24)")
    // compilation of fac
    checkcode(s"""
    (let evalc   $evalc_src
    (let fac_src (quote $fac_src)
    ((evalc fac_src) (lambda _ f f))))""",
    // confirming Figure 7 (right)
    """(lambda f0 x1 
  (lambda f2 x3 
    (let x4 (eq? x1 0) 
    (if x4 (x3 1) 
    
      (let x5 (- x1 1) 
      (let x6 (f0 x5) 
      (let x7 
        (lambda f7 x8 
          (let x9 (* x1 x8) (x3 x9))) (x6 x7))))))))""")
    checkrun(s"""
    (let evalc   $evalc_src
    (let fac_src (quote $fac_src)
    (((run 0 ((evalc fac_src) (lambda _ f f))) 4) (lambda _ x x))))""", "Cst(24)")

    val nested_src = "(lambda f n (if (if n 0 1) 2 3))"
    checkrun(s"""
    (let eval $eval_src
    (let nested_src (quote $nested_src)
    ((eval nested_src) (lambda _ f ((f 0) (lambda _ x x))))))""", "Cst(2)")
    checkcode(s"""
    (let evalc $evalc_src
    (let nested_src (quote $nested_src)
    ((evalc nested_src) (lambda _ f f))))""", """(lambda f0 x1 
  (lambda f2 x3 
    (if x1 
      (if 0 (x3 2) 
      (x3 3)) 
    
      (if 1 (x3 2) 
      (x3 3)))))""")
    checkrun(s"""
    (let evalc $evalc_src
    (let nested_src (quote $nested_src)
    (((run 0 ((evalc nested_src) (lambda _ f f))) 0) (lambda _ x x))))""", "Cst(2)")

    testDone()
  }

 def addCases(cs: String*): String = {
    val app_case = "(((eval (cadr exp)) env) (lambda _ v2 (((env (car exp)) v2) (maybe-lift (lambda _ x (k x))))))"
    ev_poly_src.replace(app_case, cs.mkString("\n")+"\n"+app_case+(")"*cs.length))
  }

  val ev0_poly_src = addCases(
    "(if (eq? 'EM (car exp)) (run (maybe-lift 0) (trans (car (cdr exp))))")
  val evn_poly_src = addCases(
    "(if (eq? 'EM (car exp)) (let e (car (cdr exp)) (EM ((eval (env 'e)) env)))")

  val eval0_src = ev_nil(ev_nolift(ev0_poly_src))
  val evaln_src = ev_nil(ev_nolift(evn_poly_src))

  // 5.1.3 Language Extensions in User Code
  // defining call/cc in terms of EM
  val emt_src = """(let call/cc (lambda _ f (EM (
((env 'f) (maybe-lift (lambda _ v (maybe-lift (lambda _ k1 (k1 (k v)))))))
(maybe-lift (lambda _ x x)))))

(+ 3 (call/cc (lambda _ k (k (k (k 1)))))))
"""
  def testEM() = {
    println("EM...")

    // sanity check
    checkrun(s"""
    (let eval0   $eval0_src
    (let fac_src (quote $fac_src)
    ((eval0 fac_src) (lambda _ f ((f 4) (lambda _ x x))))))""", "Cst(24)")

    // test call/cc
    checkrun(s"""
    (let eval0   $eval0_src
    (let emt_src (quote $emt_src)
    ((eval0 emt_src) (lambda _ x x))))""", "Cst(10)")

    testDone()
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
    (if (eq? 'clambda (car exp))        (run 0 (((eval (cons (lambda _ e (lift e)) 1)) (cons 'lambda (cdr exp)))  (lambda _ y (lift-ref (env y)))))
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
    (if (eq?  'run    (car exp))   (run (((eval l) (cadr exp)) env) (((eval l) (caddr exp)) env))
    (if (eq?  'log    (car exp))   (log (((eval l) (cadr exp)) env) (((eval l) (caddr exp)) env))
    (if (eq?  'EM     (car exp))   (run ((car l) 0) (trans (car (cdr exp))))
    (if (eq?  'trans (car exp))   (trans (cadr exp))
    ((env (car exp)) (((eval l) (cadr exp)) env)))))))))))))))))))))))
  ((((eval l) (car exp)) env) (((eval l) (cadr exp)) env)))))))))
"""

  val ev_tie_src = s"""(lambda eval l (lambda _ e ((($ev_poly_src eval) l) e)))"""
  val ev_src = s"""($ev_tie_src (cons (lambda _ e e) 0))"""
  val evc_src = s"""($ev_tie_src (cons (lambda _ e (lift e)) 1))"""
  val eval_src = ev_nil(ev_src)
  val evalc_src = ev_nil(evc_src)
  val fc_src = fac_src.replace("lambda", "clambda")

  def test_clambda() = {
    println("clambda...")

    // fac as clambda
    checkrun(s"""
    (let eval $eval_src
    (let fc_src (quote $fc_src)
    ((eval fc_src) 4)))""", "Cst(24)")

    // fac as clambda -- check compiled code
    val c_fc = ev(s"""
    (let eval $eval_src
    (let fc_src (quote $fc_src)
    (eval fc_src)))""").asInstanceOf[Clo]
    check(pretty(c_fc.e, List.fill(c_fc.env.length)("<?>")++List("r", "n")))("""(let x16 (eq? n 0) 
(if x16 1 

  (let x17 (- n 1) 
  (let x18 (r x17) (* n x18)))))""") // all interpretation overhead is gone

    // more clambda tests
    checkrun(s"((($eval_src (quote ( lambda _ x (clambda _ y (* (+ x x) y))))) 1) 4)", "Cst(8)")
    checkrun(s"((($eval_src (quote (clambda _ x ( lambda _ y (* (+ x x) y))))) 1) 4)", "Cst(8)")
    checkrun(s"((($eval_src (quote (clambda _ x (clambda _ y (* (+ x x) y))))) 1) 4)", "Cst(8)")

    checkrun(s"(($eval_src (quote (let inc (lambda _ x (+ x 1)) (clambda _ y (inc y))))) 4)", "Cst(5)")

    val f_src = "(lambda _ x (clambda _ y (lambda _ l (* (l (+ x x)) (l y)))))"
    checkrun(s"(((($eval_src (quote $f_src)) 1) 4) (lambda _ z z))", "Cst(8)")
    
    val c_f = ev(s"(($eval_src (quote $f_src)) 1)").asInstanceOf[Clo]
    check(pretty(c_f.e, List.fill(c_f.env.length)("<?>")++List("_", "y")))("""(lambda f16 x17 
  (let x18 (+ <special> <special>) 
  (let x19 (x17 x18) 
  (let x20 (x17 y) (* x19 x20)))))""")
    checkcode(s"(((($eval_src (quote $f_src)) 1) 4) (lambda _ z (lift z)))", "(* 2 4)")

    testDone()
  }

  def test_em() {
    println("EM...")

    // implement logging with EM
    val ev_log_src = ev_tie_src.replace("(env exp)", "(if (eq? 'n exp) (log ((car l) 0) (env exp)) (env exp))")
    val fac4_trace = "Cst(4);Cst(4);Cst(4);Cst(3);Cst(3);Cst(3);Cst(2);Cst(2);Cst(2);Cst(1);Cst(1);Cst(1);Cst(0);"
    def em1(src: String) = s"(EM ((($ev_log_src l) '($src 4)) env))"
    def em2(src: String) = s"""(EM ((((lambda ev l (lambda _ exp (lambda _ env
    (if (if (sym? exp) (eq? 'n exp) 0) (log ((car l) 0) (((eval l) exp) env))
    ((((tie ev) l) exp) env))))) l) '($src 4)) env))"""

    checkrunlog(s"($eval_src '${em1(fac_src)})", "Cst(24)", fac4_trace)
    checkrunlog(s"($eval_src '${em1(fc_src)})" , "Cst(24)", fac4_trace)
    checkrunlog(s"($eval_src '${em2(fac_src)})", "Cst(24)", fac4_trace)
    checkrunlog(s"($eval_src '${em2(fc_src)})" , "Cst(24)", fac4_trace)

    testDone()
  }

  def test() = {
    println("// ------- Pink_clambda.test --------")
    test_clambda()
    test_em()
  }
}
