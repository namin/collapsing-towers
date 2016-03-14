object Lisp {
  import Base._

  import scala.util.parsing.combinator._

  // from github.com/namin/lms-black
  object parser extends JavaTokenParsers with PackratParsers {
    override val whiteSpace = """(\s|(;[^\n]*))+""".r

    def S(x:String) = Str(x)
    def Str2(x:String) = ???
    def P(x:Val,y:Val) = Tup(x,y)
    def B(x:Boolean) = ???
    def I(x:Int) = Cst(x)
    val N = Str(".")

    lazy val exp: Parser[Val] =
        "#f" ^^ { case _ => B(false) } |
        "#t" ^^ { case _ => B(true) } |
        wholeNumber ^^ { case s => I(s.toInt) } |
        """[^\s\(\)'"]+""".r ^^ { case s => S(s) } |
        stringLiteral ^^ { case s => Str2(s.substring(1, s.length-1)) } |
        "'" ~> exp ^^ { case s => P(S("quote"), P(s, N)) } |
        "()" ^^ { case _ => N } |
        "(" ~> exps <~ ")" ^^ { case vs => vs }

    lazy val exps: Parser[Val] =
        exp ~ opt(exps) ^^ { case v~Some(vs) => P(v, vs) case v~None => P(v,N) }
  }


  import parser._

  /* 
    TODO:
      + fix parser perf problems
      + proper var names
      + double interpretation
      + pretty printing
      + double code generation
      - use right-to-left de brujin indexes to make closures ctx-independent
          (not so simple b/c let insertion)
  */

  // ********************* convert exp encoded as val --> exp  *********************

  def trans(e: Val, env: List[String]): Exp = e match {
    case Cst(n) => Lit(n)
    case Str(s) => val i = env.lastIndexOf(s); assert(i>=0, s); Var(i)
    case Tup(Str("quote"),Tup(Str(s),N)) => Sym(s)
    case Tup(Str("+"),Tup(a,Tup(b,N))) => Plus(trans(a,env),trans(b,env))
    case Tup(Str("-"),Tup(a,Tup(b,N))) => Minus(trans(a,env),trans(b,env))
    case Tup(Str("*"),Tup(a,Tup(b,N))) => Times(trans(a,env),trans(b,env))
    // (let x a b)
    case Tup(Str("let"),Tup(Str(x),Tup(a,Tup(b,N)))) => Let(trans(a,env),trans(b,env:+x))
    // (lambda f x e)
    case Tup(Str("lambda"),Tup(Str(f),Tup(Str(x),Tup(e,N)))) => Lam(trans(e,env:+f:+x))
    case Tup(Str("if"),Tup(c,Tup(a,Tup(b,N)))) => If(trans(c,env),trans(a,env),trans(b,env))
    case Tup(Str("isNum"),Tup(a,N)) => IsNum(trans(a,env))
    case Tup(Str("isStr"),Tup(a,N)) => IsStr(trans(a,env))
    case Tup(Str("cons"),Tup(a,Tup(b,N))) => Pair(trans(a,env),trans(b,env))
    case Tup(Str("car"),Tup(a,N)) => Fst(trans(a,env))
    case Tup(Str("cdr"),Tup(a,N)) => Snd(trans(a,env))
    case Tup(Str("lift"),Tup(a,N)) => Lift(trans(a,env))
    case Tup(Str("lift-ref"),Tup(a,N)) => LiftRef(trans(a,env))
    case Tup(Str("nolift"),Tup(a,N)) => trans(a,env)
    case Tup(Str("nolift-ref"),Tup(a,N)) => trans(a,env)
    case Tup(Str("equs"),Tup(a,Tup(b,N))) => Equs(trans(a,env),trans(b,env))
    case Tup(Str("refNew"),Tup(a,N)) => RefNew(trans(a,env))
    case Tup(Str("refRead"),Tup(a,N)) => RefRead(trans(a,env))
    case Tup(Str("refWrite"),Tup(a,Tup(e,N))) => RefWrite(trans(a,env),trans(e,env))
    // special forms: eval / trans assume empty env for now
    case Tup(Str("exec"),Tup(a,N)) => 
      Special(benv => evalms(Nil, reifyc(evalms(benv, trans(a,env)))))
    case Tup(Str("trans-quote"),Tup(a,N)) => 
      Special(benv => Code(trans(evalms(benv, trans(a,env)), Nil)))
    case Tup(Str("quote"),Tup(a,N)) => Special(benv => a)
    // generic app
    case Tup(a,Tup(b,N)) => App(trans(a,env),trans(b,env))
  }


  // ********************* source programs  *********************

  val fac_src = "(lambda f n (if n (* n (f (- n 1))) 1))"
  val mut_src = "(let c (refNew 0) (lambda _ n (refRead (refWrite c (- (refRead (refWrite c (+ (refRead c) 28))) n)))))"

  val eval_poly_src = """
  (lambda eval exp (lambda _ env
    (if (isNum               exp)       (maybe-lift exp)
    (if (isStr               exp)       (env exp)
    (if (isStr          (car exp))      
      (if (equs '+      (car exp))      (+  ((eval (cadr exp)) env) ((eval (caddr exp)) env))
      (if (equs '-      (car exp))      (-  ((eval (cadr exp)) env) ((eval (caddr exp)) env))
      (if (equs '*      (car exp))      (*  ((eval (cadr exp)) env) ((eval (caddr exp)) env))
      (if (equs 'equs   (car exp))      (equs ((eval (cadr exp)) env) ((eval (caddr exp)) env))
      (if (equs 'if     (car exp))      (if ((eval (cadr exp)) env) ((eval (caddr exp)) env) ((eval (cadddr exp)) env))
      (if (equs 'lambda (car exp))      (maybe-lift (lambda f x ((eval (cadddr exp)) (lambda _ y (if (equs y (cadr exp)) f (if (equs y (caddr exp)) x (env y)))))))
      (if (equs 'let    (car exp))      (let x ((eval (caddr exp)) env) ((eval (cadddr exp)) (lambda _ y (if (equs y (cadr exp)) x (env y)))))
      (if (equs 'lift       (car exp))      (lift       ((eval (cadr exp)) env))
      (if (equs 'lift-ref   (car exp))      (lift-ref   ((eval (cadr exp)) env))
      (if (equs 'nolift     (car exp))      (nolift     ((eval (cadr exp)) env))
      (if (equs 'nolift-ref (car exp))      (nolift-ref ((eval (cadr exp)) env))
      (if (equs 'isNum  (car exp))      (isNum ((eval (cadr exp)) env))
      (if (equs 'isStr  (car exp))      (isStr ((eval (cadr exp)) env))
      (if (equs 'cons   (car exp))      (maybe-lift (cons ((eval (cadr exp)) env) ((eval (caddr exp)) env)))
      (if (equs 'car    (car exp))      (car ((eval (cadr exp)) env))
      (if (equs 'cdr    (car exp))      (cdr ((eval (cadr exp)) env))
      (if (equs 'quote  (car exp))      (maybe-lift (cadr exp))
      (if (equs 'refNew (car exp))      (maybe-lift (refNew ((eval (cadr exp)) env)))
      (if (equs 'refRead (car exp))     (refRead ((eval (cadr exp)) env))
      (if (equs 'refWrite (car exp))    (refWrite ((eval (cadr exp)) env) ((eval (caddr exp)) env))
      ((env (car exp)) ((eval (cadr exp)) env))))))))))))))))))))))
    (((eval (car exp)) env) ((eval (cadr exp)) env))
    )))))""".
    replace("(cadr exp)","(car (cdr exp))").
    replace("(caddr exp)","(car (cdr (cdr exp)))").
    replace("(cadddr exp)","(car (cdr (cdr (cdr exp))))")

  val eval_vc_poly_src = s"""(lambda _ c
${eval_poly_src.replace("(env exp)", "(let _ (if (equs 'n exp) (refWrite c (+ (refRead c) (trace-lift 1))) (trace-lift 0)) (env exp))")}
)
"""

  val eval_src = eval_poly_src.replace("maybe-lift","nolift") // plain interpreter
  val evalc_src = eval_poly_src.replace("maybe-lift","lift")  // generating extension = compiler

  val eval_vc_src = eval_vc_poly_src.replace("trace-lift","nolift").replace("maybe-lift","nolift") // plain interpreter
  val evalc_vc_src = eval_vc_poly_src.replace("trace-lift","lift").replace("maybe-lift","lift")  // generating extension = compiler

  val evalt_vc_src = eval_vc_poly_src.replace("trace-lift","lift").replace("maybe-lift","nolift")  // transformer


  // TODO: next step: take maybe-lift as parameter instead of simulating macros

  // NOTE: have to be careful with 'equs': if arg is not a string, it might create a code object */

  val Success(fac_val, _) = parseAll(exp, fac_src)
  val Success(mut_val, _) = parseAll(exp, mut_src)
  val Success(eval_val, _) = parseAll(exp, eval_src)
  val Success(evalc_val, _) = parseAll(exp, evalc_src)
  val Success(eval_vc_val, _) = parseAll(exp, eval_vc_src)
  val Success(evalc_vc_val, _) = parseAll(exp, evalc_vc_src)
  val Success(evalt_vc_val, _) = parseAll(exp, evalt_vc_src)


  val fac_exp = trans(fac_val,List("arg"))
  val mut_exp = trans(mut_val,List("arg"))
  val eval_exp = trans(eval_val,List("arg","arg2"))
  val evalc_exp = trans(evalc_val,List("arg","arg2"))
  val eval_vc_exp = trans(eval_vc_val,List("arg","arg2", "arg3"))
  val evalc_vc_exp = trans(evalc_vc_val,List("arg","arg2", "arg3"))
  val evalt_vc_exp = trans(evalt_vc_val,List("arg","arg2", "arg3"))

  val fac_exp_anf = reify { anf(List(Sym("XX")),fac_exp) }
  val mut_exp_anf = reify { anf(List(Sym("XX")),mut_exp) }
  val eval_exp_anf = reify { anf(List(Sym("XX"),Sym("XX")),eval_exp) }
  val evalc_exp_anf = reify { anf(List(Sym("XX"),Sym("XX")),evalc_exp) }
  val eval_vc_exp_anf = reify { anf(List(Sym("XX"),Sym("XX"),Sym("XX")),eval_vc_exp) }
  val evalc_vc_exp_anf = reify { anf(List(Sym("XX"),Sym("XX"),Sym("XX")),evalc_vc_exp) }
  val evalt_vc_exp_anf = reify { anf(List(Sym("XX"),Sym("XX"),Sym("XX")),evalt_vc_exp) }


  // ********************* test cases *********************

  def testEval() = {
    println("// ------- test eval --------")

    check(fac_exp_anf)("Let(Lam(Let(If(Var(1),Let(Minus(Var(1),Lit(1)),Let(App(Var(0),Var(2)),Let(Times(Var(1),Var(3)),Var(4)))),Lit(1)),Var(2))),Var(0))")


    // -----------------------------------------------
    // interpretation

    val r1 = run { evalms(List(fac_val,eval_val),App(App(App(eval_exp,Var(0)),Sym("nil-env")),Lit(4))) }

    check(r1)("Cst(24)")


    // generation + interpretation

    val c1 = reifyc { evalms(List(fac_val,eval_val),App(App(evalc_exp,Var(0)),Sym("nil-env"))) }

    check(c1)(fac_exp_anf.toString)

    val r2 = run { evalms(Nil,App(c1,Lit(4))) }

    check(r2)("Cst(24)")

    // we can show:
    // (evalms (evalc fac)) = fac
    // (evalms (evalc eval)) = eval
    // (evalms (evalc evalc)) = evalc



    // -----------------------------------------------
    // double interpretation!!

    // first try a plain value ... (evalms ((eval eval) 24)) = 24
    val r3 = run { evalms(List(fac_val,eval_val), App(App(App(App(eval_exp,Var(1)),Sym("nil-env")), Lit(24)), Sym("nil-env2"))) }

    check(r3)("Cst(24)")


    // double eval fac ... (evalms (((eval eval) fac) 4)) = 24
    val r4 = run { evalms(List(fac_val,eval_val), App(App(App(App(App(eval_exp,Var(1)),Sym("nil-env")), Var(0)), Sym("nil-env2")), Lit(4))) }

    check(r4)("Cst(24)")


    // code generation through double interpretation !!!  (evalms ((eval evalc) fac)) = fac

    val c2 = reifyc { evalms(List(fac_val,evalc_val), App(App(App(App(eval_exp,Var(1)),Sym("nil-env")), Var(0)), Sym("nil-env2"))) }

    check(c2)(fac_exp_anf.toString)

    val r5 = run { evalms(Nil,App(c2,Lit(4))) }

    check(r5)("Cst(24)")



    // now generate evaluator ... (evalms ((eval evalc) eval)) = eval

    val c3 = reifyc { evalms(List(eval_val,evalc_val), App(App(App(App(eval_exp,Var(1)),Sym("nil-env")), Var(0)), Sym("nil-env2"))) }

    // this is our evaluator!!!  
    // println("--- decompiled eval ---")
    // println(pretty(c3,Nil)) 
    //check(c3)(eval_exp_anf.toString)
    check(pretty(c3,Nil))(pretty(eval_exp_anf,Nil).toString) // compare prettyprinted b/c extra let

    // test that we can use the evaluator to run fac
    // NOTE: cannot put fac_val intro env!! 
    val r6 = run { val eval_val3 = evalms(Nil,c3); evalms(List(eval_val3,fac_val),App(App(App(Var(0),Var(1)), Sym("nil-env")), Lit(4))) }

    check(r6)("Cst(24)")



    // now generate generator ... (evalms ((eval evalc) evalc)) = evalc

    val c4 = reifyc { evalms(List(eval_val,evalc_val), App(App(App(App(eval_exp,Var(1)),Sym("nil-env")), Var(1)), Sym("nil-env2"))) }

    // this is our generator!!!
    // println("--- decompiled evalc ---")
    // println(pretty(c4,Nil))
    //check(c4)(evalc_exp_anf.toString)
    check(pretty(c4,Nil))(pretty(evalc_exp_anf,Nil).toString) // compare prettyprinted b/c extra let

    val c5 = reifyc { val eval_valc4 = evalms(Nil,c4); evalms(List(eval_valc4,fac_val),App(App(Var(0),Var(1)), Sym("nil-env"))) }


    // this is fac, generated by decompiled evalc
    // println("--- fac generated by decompiled evalc ---")
    // println(pretty(c5,Nil)) 
    check(c5)(fac_exp_anf.toString)

    val r7 = run { evalms(Nil,App(c5,Lit(4))) }

    check(r7)("Cst(24)")

    // we have:
    // (evalms ((eval evalc) fac)) = fac
    // (evalms ((eval evalc) eval) = eval
    // (evalms ((eval evalc) evalc) = evalc


    // -----------------------------------------------
    // triple interpretation!!

    val eval_exp3 = trans(eval_val,List("arg","arg2","arg3")) // need three slots in env...

    // triple eval fac ... (evalms (((eval eval) evalc) fac)) = fac
    val c6 = reifyc { evalms(List(evalc_val,eval_val,fac_val), 
      App(App(App(App(App(App(App(App(eval_exp3,Var(1)),Sym("nil-env")), Var(1)), Sym("nil-env2")), Var(0)), Sym("nil-env3")), Var(2)), Sym("nil-env4"))) }

    check(c6)(fac_exp_anf.toString)
  }

  def testMutEval() = {
    println("// ------- test mutation eval --------")

    // -----------------------------------------------
    // interpretation

    val r1 = run { evalms(List(mut_val,eval_val),App(App(App(eval_exp,Var(0)),Sym("nil-env")),Lit(4))) }

    check(r1)("Cst(24)")


    // generation + interpretation

    val c1 = reifyc { evalms(List(mut_val,eval_val),App(App(evalc_exp,Var(0)),Sym("nil-env"))) }

    check(c1)(mut_exp_anf.toString)

    val r2 = run { evalms(Nil,App(c1,Lit(4))) }

    check(r2)("Cst(24)")

    // we can show:
    // (evalms (evalc mut)) = mut
    // (evalms (evalc eval)) = eval
    // (evalms (evalc evalc)) = evalc



    // -----------------------------------------------
    // double interpretation!!

    // first try a plain value ... (evalms ((eval eval) 24)) = 24
    val r3 = run { evalms(List(mut_val,eval_val), App(App(App(App(eval_exp,Var(1)),Sym("nil-env")), Lit(24)), Sym("nil-env2"))) }

    check(r3)("Cst(24)")


    // double eval mut ... (evalms (((eval eval) mut) 4)) = 24
    val r4 = run { evalms(List(mut_val,eval_val), App(App(App(App(App(eval_exp,Var(1)),Sym("nil-env")), Var(0)), Sym("nil-env2")), Lit(4))) }

    check(r4)("Cst(24)")


    // code generation through double interpretation !!!  (evalms ((eval evalc) mut)) = mut

    val c2 = reifyc { evalms(List(mut_val,evalc_val), App(App(App(App(eval_exp,Var(1)),Sym("nil-env")), Var(0)), Sym("nil-env2"))) }

    check(c2)(mut_exp_anf.toString)

    val r5 = run { evalms(Nil,App(c2,Lit(4))) }

    check(r5)("Cst(24)")



    // now generate evaluator ... (evalms ((eval evalc) eval)) = eval

    val c3 = reifyc { evalms(List(eval_val,evalc_val), App(App(App(App(eval_exp,Var(1)),Sym("nil-env")), Var(0)), Sym("nil-env2"))) }

    // this is our evaluator!!!  
    // println("--- decompiled eval ---")
    // println(pretty(c3,Nil)) 
    //check(c3)(eval_exp_anf.toString)
    check(pretty(c3,Nil))(pretty(eval_exp_anf,Nil).toString) // compare prettyprinted b/c extra let

    // test that we can use the evaluator to run mut
    // NOTE: cannot put mut_val intro env!! 
    val r6 = run { val eval_val3 = evalms(Nil,c3); evalms(List(eval_val3,mut_val),App(App(App(Var(0),Var(1)), Sym("nil-env")), Lit(4))) }

    check(r6)("Cst(24)")



    // now generate generator ... (evalms ((eval evalc) evalc)) = evalc

    val c4 = reifyc { evalms(List(eval_val,evalc_val), App(App(App(App(eval_exp,Var(1)),Sym("nil-env")), Var(1)), Sym("nil-env2"))) }

    // this is our generator!!!
    // println("--- decompiled evalc ---")
    // println(pretty(c4,Nil))
    //check(c4)(evalc_exp_anf.toString)
    check(pretty(c4,Nil))(pretty(evalc_exp_anf,Nil).toString) // compare prettyprinted b/c extra let

    val c5 = reifyc { val eval_valc4 = evalms(Nil,c4); evalms(List(eval_valc4,mut_val),App(App(Var(0),Var(1)), Sym("nil-env"))) }


    // this is mut, generated by decompiled evalc
    // println("--- mut generated by decompiled evalc ---")
    // println(pretty(c5,Nil)) 
    check(c5)(mut_exp_anf.toString)

    val r7 = run { evalms(Nil,App(c5,Lit(4))) }

    check(r7)("Cst(24)")

    // we have:
    // (evalms ((eval evalc) mut)) = mut
    // (evalms ((eval evalc) eval) = eval
    // (evalms ((eval evalc) evalc) = evalc


    // -----------------------------------------------
    // triple interpretation!!

    val eval_exp3 = trans(eval_val,List("arg","arg2","arg3")) // need three slots in env...

    // triple eval mut ... (evalms (((eval eval) evalc) mut)) = mut
    val c6 = reifyc { evalms(List(evalc_val,eval_val,mut_val), 
      App(App(App(App(App(App(App(App(eval_exp3,Var(1)),Sym("nil-env")), Var(1)), Sym("nil-env2")), Var(0)), Sym("nil-env3")), Var(2)), Sym("nil-env4"))) }

    check(c6)(mut_exp_anf.toString)
  }

  def testMutInEval() = {
    println("// ------- test mutation in eval --------")
    val counter_cell = new Cell(Cst(0))

    // -----------------------------------------------
    // interpretation
    val r1 = run { evalms(List(fac_val,eval_val,counter_cell),
      App(App(App(App(eval_vc_exp,Var(2)),Var(0)),Sym("nil-env")),Lit(4))) }
    check(r1)("Cst(24)")
    check(counter_cell.v)("Cst(13)")
    counter_cell.v = Cst(0)

    // generation + interpretation
    val c1 = reifyc { evalms(List(fac_val,eval_val,counter_cell),App(App(App(evalc_vc_exp,LiftRef(Var(2))),Var(0)),Sym("nil-env"))) }
    val expected = """
    |fun f0 x1 
    |  let x2 = RefExt(Base$Cell@XX)! in 
    |  let x3 = (x2 + 1) in 
    |  let x4 = (RefExt(Base$Cell@XX) := x3) in 
    |  if (x1) 
    |    let x5 = RefExt(Base$Cell@XX)! in 
    |    let x6 = (x5 + 1) in 
    |    let x7 = (RefExt(Base$Cell@XX) := x6) in 
    |    let x8 = RefExt(Base$Cell@XX)! in 
    |    let x9 = (x8 + 1) in 
    |    let x10 = (RefExt(Base$Cell@XX) := x9) in 
    |    let x11 = (x1 - 1) in 
    |    let x12 = (f0 x11) in (x1 * x12) 
    |  else 1""".stripMargin
    check(pretty(c1, Nil).replaceAll("@[0-9a-f]+","@XX"))(expected)
    check(counter_cell.v)("Cst(0)")
    val r2 = run { evalms(Nil,App(c1,Lit(4))) }
    check(r2)("Cst(24)")
    check(counter_cell.v)("Cst(13)")
  }


  def testEvalSyntax() = {
    println("// ------- test eval from lisp syntax --------")

    def run(src: String) = {
      val prog_src = s"""(let exec-quote (lambda _ src (exec (trans-quote src))) $src)"""
      val Success(prog_val, _) = parseAll(exp, prog_src)
      val prog_exp = trans(prog_val,Nil)
      val res = reifyv(evalms(Nil,prog_exp))
      println(res)
      res
    }

    // plain exec
    run(s"""(let fac $fac_src (fac 4))""")

    // quote + exec
    run(s"""
    (let fac_val (quote $fac_src)
    (let fac     (exec-quote fac_val)
    (fac 4)))""")

    // quote + interpret
    run(s"""
    (let fac_val       (quote $fac_src)
    (let eval_poly     (lambda _ maybe-lift (lambda _ exp (($eval_poly_src exp) 'nil)))
    (let eval          (eval_poly (lambda _ e e))
    (let fac           (eval fac_val)
    (fac 4)))))""")

    // quote + compile
    run(s"""
    (let fac_val       (quote $fac_src)
    (let eval_poly     (lambda _ maybe-lift (lambda _ exp (($eval_poly_src exp) 'nil)))
    (let evalc         (eval_poly (lambda _ e (lift e)))
    (let fac           (exec (evalc fac_val)) ; evalc call must be in arg position (reify!)
    (fac 4)))))""")

    // quote + compile with interpreted compiler
    run(s"""
    (let fac_val       (quote $fac_src)
    (let eval_poly_val (quote (lambda _ maybe-lift (lambda _ exp (($eval_poly_src exp) 'nil))))
    (let eval_poly     (exec-quote eval_poly_val)
    (let eval          (eval_poly (lambda _ e e))
    (let eval_poly2    (eval eval_poly_val)
    (let evalc2        (eval_poly2 (lambda _ e (lift e)))
    (let fac           (exec (evalc2 fac_val))
    (fac 4))))))))""")

  }

}
