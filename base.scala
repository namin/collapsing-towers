/* collapsing multiple levels of interpreters */

object TestMeta3 {

  abstract class Exp
  case class Lit(n:Int) extends Exp
  case class Sym(s:String) extends Exp
  case class Var(n:Int) extends Exp
  case class App(e1:Exp, e2:Exp) extends Exp
  case class Lam(e:Exp) extends Exp
  case class Let(e1:Exp,e2:Exp) extends Exp
  case class If(c:Exp,a:Exp,b:Exp) extends Exp
  case class Plus(a:Exp,b:Exp) extends Exp
  case class Minus(a:Exp,b:Exp) extends Exp
  case class Times(a:Exp,b:Exp) extends Exp
  case class Equs(a:Exp,b:Exp) extends Exp
  case class Pair(a:Exp,b:Exp) extends Exp
  case class Fst(a:Exp) extends Exp
  case class Snd(a:Exp) extends Exp
  case class IsNum(a:Exp) extends Exp
  case class IsStr(a:Exp) extends Exp
  case class IsPair(a:Exp) extends Exp
  case object Tic extends Exp

  case class Lift(e:Exp) extends Exp
  case object Tic2 extends Exp


  type Env = List[Val]

  abstract class Val
  case class Cst(n:Int) extends Val
  case class Str(s:String) extends Val
  case class Clo(env:Env,e:Exp) extends Val //{ override def toString="CLO"}
  case class Tup(v1:Val,v2:Val) extends Val

  case class Code(e:Exp) extends Val

  var stC = 0
  def tick() = { stC += 1; stC - 1 }

  // regular evaluation (subset)
  def eval(env: Env, e: Exp): Val = e match {
    case Lit(n) => Cst(n)
    case Var(n) => env(n)
    case App(e1,e2) =>
      val Clo(env3,e3) = eval(env,e1)
      val v2 = eval(env,e2)
      eval(env3:+Clo(env3,e3):+v2,e3)
    case Lam(e) => Clo(env,e)
    case Let(e1,e2) => 
      val v1 = eval(env,e1)
      eval(env:+v1,e2)
    case Tic => 
      Cst(tick())
  }

  var stFresh = 0
  var stBlock: List[Exp] = Nil
  var stFun: List[(Int,Env,Exp)] = Nil
  def run[A](f: => A): A = {
    val sF = stFresh
    val sB = stBlock
    val sN = stFun
    try f finally { stFresh = sF; stBlock = sB; stFun = sN }
  }

  def fresh() = {
    stFresh += 1; Var(stFresh-1)
  }
  def reify(f: => Exp) = run {
    stBlock = Nil
    val last = f
    (stBlock foldRight last)(Let)
  }
  def reflect(s:Exp) = {
    stBlock :+= s
    fresh()
  }

  // regular anf conversion
  def anf(env: List[Exp], e: Exp): Exp = e match {
    case Lit(n) => Lit(n)
    case Sym(n) => Sym(n)
    case Var(n) => env(n)
    case App(e1,e2) =>
      reflect(App(anf(env,e1),anf(env,e2)))
    case Lam(e) => 
      reflect(Lam(reify(anf(env:+fresh():+fresh(),e))))
    case Let(e1,e2) => 
      anf(env:+(anf(env,e1)),e2)
    case If(c,a,b) => 
      reflect(If(anf(env,c),reify(anf(env,a)),reify(anf(env,b))))
    case Plus(e1,e2) =>
      reflect(Plus(anf(env,e1),anf(env,e2)))
    case Times(e1,e2) =>
      reflect(Times(anf(env,e1),anf(env,e2)))
    case Minus(e1,e2) =>
      reflect(Minus(anf(env,e1),anf(env,e2)))
    case Equs(e1,e2) =>
      reflect(Equs(anf(env,e1),anf(env,e2)))
    case IsNum(e) =>
      reflect(IsNum(anf(env,e)))
    case IsStr(e) =>
      reflect(IsStr(anf(env,e)))
    case Fst(e) =>
      reflect(Fst(anf(env,e)))
    case Snd(e) =>
      reflect(Snd(anf(env,e)))
    case Lift(e) =>
      reflect(Lift(anf(env,e)))
    case Tic => 
      reflect(Tic)
  }


  def reifyc(f: => Val) = reify { val Code(e) = f; e }
  def reflectc(s: Exp) = Code(reflect(s))

  // NBE-style 'reify' operator (semantics -> syntax)
  def lift(v: Val): Exp = v match {
    case Cst(n) => // number
      Lit(n)
    case Str(s) => // string
      Sym(s)
    case Tup(a,b) =>
      Pair(lift(a),lift(b))
    case Clo(env2,e2) => // function
      //println("??" + v)
      stFun collectFirst { case (n,`env2`,`e2`) => n } match {
        case Some(n) =>
          Var(n)
        case None =>
          stFun :+= (stFresh,env2,e2)
          //reflect(Lam(reify{ fresh(); val Code(r) = evalms(env2:+(Clo(env2,e2)):+Code(fresh()),e2); r }))
          // TODO: line above corresponds directly to Scala/LMS. but our intention is to do the right thing for `this` anyways:
          reflect(Lam(reify{ val Code(r) = evalms(env2:+Code(fresh()):+Code(fresh()),e2); r }))
      }
    case Code(e) => Lift(e)
      // Here is a choice: should lift be idempotent? 
      // In this case we would return e. 
      // This seems to imply that we can have only 2 stages.
      // If we would like to support more, we need to return Lift(e)
  }

  // multi-stage evaluation
  def evalms(env: Env, e: Exp): Val = e match {
    case Lit(n) => Cst(n)
    case Sym(s) => Str(s)
    case Var(n) => env(n)
    case Lam(e) => Clo(env,e)
    case Let(e1,e2) => 
      val v1 = evalms(env,e1)
      evalms(env:+v1,e2)
    case Tic => 
      Cst(tick())

    case Lift(e) => 
      Code(lift(evalms(env,e)))
    case Tic2 => 
      Code(reflect(Tic))

    case App(e1,e2) =>
      (evalms(env,e1), evalms(env,e2)) match {
        case (Clo(env3,e3), v2) => 
          evalms(env3:+Clo(env3,e3):+v2,e3)
        case (Code(s1), Code(s2)) =>
          Code(reflect(App(s1,s2)))
      }

    case If(c,a,b) =>
      evalms(env,c) match {
        case Cst(n) => 
          if (n != 0) evalms(env,a) else evalms(env,b)
        case (Code(c1)) =>
          reflectc(If(c1, reifyc(evalms(env,a)), reifyc(evalms(env,b))))
      }

    case Plus(e1,e2) =>
      (evalms(env,e1), evalms(env,e2)) match {
        case (Cst(n1), Cst(n2)) =>
          Cst(n1+n2)
        case (Code(s1),Code(s2)) =>
          reflectc(Plus(s1,s2))
      }
    case Minus(e1,e2) =>
      (evalms(env,e1), evalms(env,e2)) match {
        case (Cst(n1), Cst(n2)) =>
          Cst(n1-n2)
        case (Code(s1),Code(s2)) =>
          reflectc(Minus(s1,s2))
      }
    case Times(e1,e2) =>
      (evalms(env,e1), evalms(env,e2)) match {
        case (Cst(n1), Cst(n2)) =>
          Cst(n1*n2)
        case (Code(s1),Code(s2)) =>
          reflectc(Times(s1,s2))
      }
    case Equs(e1,e2) =>
      (evalms(env,e1), evalms(env,e2)) match {
        case (Str(s1), Str(s2)) =>
          Cst(if (s1 == s2) 1 else 0)
        case (Code(s1),Code(s2)) =>
          reflectc(Equs(s1,s2))
      }
    case Fst(e1) =>
      (evalms(env,e1)) match {
        case (Tup(a,b)) => 
          a
        case (Code(s1)) =>
          Code(reflect(Fst(s1)))
      }
    case Snd(e1) =>
      (evalms(env,e1)) match {
        case (Tup(a,b)) => 
          b
        case (Code(s1)) =>
          Code(reflect(Snd(s1)))
      }
    case IsNum(e1) =>
      (evalms(env,e1)) match {
        case (Code(s1)) =>
          Code(reflect(IsNum(s1)))
        case v => 
          Cst(if (v.isInstanceOf[Cst]) 1 else 0)
      }
    case IsStr(e1) =>
      (evalms(env,e1)) match {
        case (Code(s1)) =>
          Code(reflect(IsStr(s1)))
        case v => 
          Cst(if (v.isInstanceOf[Str]) 1 else 0)
      }
  }


  def check(a:Any)(s:String) = if (a.toString != s) {
    println("error: expected ")
    println("    "+s)
    println("but got")
    println("    "+a)
    (new AssertionError).printStackTrace
  }


  def testBasic() = {
    println("// ------- basic tests --------")

    val p = App(Lam(Let(Tic,Let(Tic,Var(1)))),Lit(3))
    check(p)("App(Lam(Let(Tic,Let(Tic,Var(1)))),Lit(3))")

    check(eval(Nil,p))("Cst(3)")

    val p2 = reify(anf(Nil,p))
    check(p2)("Let(Lam(Let(Tic,Let(Tic,Var(1)))),Let(App(Var(0),Lit(3)),Var(1)))")

    check(eval(Nil,p2))("Cst(3)")
  }

  def testAck1() = {
    println("// ------- ackermann 1 --------")
    val a = Var(0)
    val m = Var(1)
    val n = Var(3)
    val m_sub_1 = Minus(m,Lit(1))
    val n_sub_1 = Minus(n,Lit(1))
    val n_add_1 = Plus(n,Lit(1))

/*
  def a(m: Int): Rep[Int => Int] = fun { (n: Rep[Int]) =>
    if (m==0) n+1
    else if (n==0) a(m-1)(1)
    else a(m-1)(a(m)(n-1))
  }
*/    
    val ackN = Lam(Lam(
                If(m,
                  If(n,App(App(a,m_sub_1),App(App(a,m),n_sub_1)),
                       App(App(a,m_sub_1),Lit(1))),
                  n_add_1)))
    check(evalms(Nil,App(App(ackN,Lit(2)),Lit(2))))("Cst(7)")

  }
    

  def testAck2() = {
    println("// ------- ackermann 2 --------")
    val a = Var(0)
    val m = Var(1)
    val n = Var(3)
    val m_sub_1 = Minus(m,Lit(1))
    val n_sub_1 = Minus(n,Lift(Lit(1)))
    val n_add_1 = Plus(n,Lift(Lit(1)))

/*
  def a(m: Int): Rep[Int => Int] = fun { (n: Rep[Int]) =>
    if (m==0) n+1
    else if (n==0) a(m-1)(1)
    else a(m-1)(a(m)(n-1))
  }
*/    

    val ackN = Lam(Lift(Lam(
                If(m,
                  If(n,App(App(a,m_sub_1),App(App(a,m),n_sub_1)),
                       App(App(a,m_sub_1),Lift(Lit(1)))),
                  n_add_1))))
    val code = reifyc(evalms(Nil,App(App(ackN,Lit(2)),Lift(Lit(2)))))

    val out = 
      Let(Lam(
        Let(If(Var(1),
          Let(Lam(Let(If(Var(3),
            Let(Lam(Let(Plus(Var(5),Lit(1)),Var(6))),Let(Minus(Var(3),Lit(1)),Let(App(Var(2),Var(5)),Let(App(Var(4),Var(6)),Var(7))))),
            Let(Lam(Let(Plus(Var(5),Lit(1)),Var(6))),Let(App(Var(4),Lit(1)),Var(5)))
            ),Var(4))),Let(Minus(Var(1),Lit(1)),Let(App(Var(0),Var(3)),Let(App(Var(2),Var(4)),Var(5))))),
          Let(Lam(Let(If(Var(3),
            Let(Lam(Let(Plus(Var(5),Lit(1)),Var(6))),Let(Minus(Var(3),Lit(1)),Let(App(Var(2),Var(5)),Let(App(Var(4),Var(6)),Var(7))))),
            Let(Lam(Let(Plus(Var(5),Lit(1)),Var(6))),Let(App(Var(4),Lit(1)),Var(5)))
            ),Var(4))),Let(App(Var(2),Lit(1)),Var(3)))
          ),Var(2))),Let(App(Var(0),Lit(2)),Var(1)))

    check(code)(out.toString)

    check(evalms(Nil,code))("Cst(7)")
  }


  def testFac1() = {
    println("// ------- factorial 1 --------")
    val f_self = App(Var(0),Lit(99))
    val n = Var(3)

/*
  pattern:
    
    def f = fun { n => if (n != 0) f(n-1) else 1 }

  corresponds to:

    val f = { () => lift({ n => if (n != 0) f()(n-1) else 1 }) }

*/

    val fac_body = Lam(If(n,Times(n,App(f_self,Minus(n,Lift(Lit(1))))),Lift(Lit(1))))

    val fac = App(Lam(Lift(fac_body)),Lit(99))

    val code = reifyc(evalms(Nil,fac))

    val out = 
      Let(Lam(
        Let(If(Var(1),
              Let(Minus(Var(1),Lit(1)),
              Let(App(Var(0),Var(2)),
              Let(Times(Var(1),Var(3)),
              Var(4)))),
            /* else */
              Lit(1)
        ),
        Var(2))),
      Var(0))

    check(code)(out.toString)

    check(evalms(Nil,App(code,Lit(4))))("Cst(24)")
  }

  import scala.util.parsing.combinator._

  // from github.com/namin/lms-black
  object parser extends JavaTokenParsers with PackratParsers {
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


  def testEval() = {
    println("// ------- test eval --------")
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


    // ********************* source programs  *********************

    val fac_src = "(lambda f n (if n (* n (f (- n 1))) 1))"

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
        (if (equs 'lift   (car exp))      (lift ((eval (cadr exp)) env))
        (if (equs 'nolift (car exp))      (nolift ((eval (cadr exp)) env))
        (if (equs 'isNum  (car exp))      (isNum ((eval (cadr exp)) env))
        (if (equs 'isStr  (car exp))      (isStr ((eval (cadr exp)) env))
        (if (equs 'car    (car exp))      (car ((eval (cadr exp)) env))
        (if (equs 'cdr    (car exp))      (cdr ((eval (cadr exp)) env))
        (if (equs 'quote  (car exp))      (maybe-lift (cadr exp))
        ((env (car exp)) ((eval (cadr exp)) env)))))))))))))))
      (((eval (car exp)) env) ((eval (cadr exp)) env))
      )))))
    """.replace("(cadr exp)","(car (cdr exp))")
       .replace("(caddr exp)","(car (cdr (cdr exp)))")
       .replace("(cadddr exp)","(car (cdr (cdr (cdr exp))))")

    val eval_src = eval_poly_src.replace("maybe-lift","nolift") // plain interpreter
    val evalc_src = eval_poly_src.replace("maybe-lift","lift")  // generating extension = compiler

    // TODO: next step: take maybe-lift as parameter instead of simulating macros

    // NOTE: have to be careful with 'equs': if arg is not a string, it might create a code object */

    val Success(fac_val, _) = parseAll(exp, fac_src)
    val Success(eval_val, _) = parseAll(exp, eval_src)
    val Success(evalc_val, _) = parseAll(exp, evalc_src)


    // ********************* convert / pretty print terms  *********************

    def trans(e: Val, env: List[String]): Exp = e match {
      case Cst(n) => Lit(n)
      case Str(s) => Var(env.lastIndexOf(s))
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
      case Tup(Str("car"),Tup(a,N)) => Fst(trans(a,env))
      case Tup(Str("cdr"),Tup(a,N)) => Snd(trans(a,env))
      case Tup(Str("lift"),Tup(a,N)) => Lift(trans(a,env))
      case Tup(Str("nolift"),Tup(a,N)) => trans(a,env)
      case Tup(Str("equs"),Tup(a,Tup(b,N))) => Equs(trans(a,env),trans(b,env))
      case Tup(a,Tup(b,N)) => App(trans(a,env),trans(b,env))
    }

    var indent = "\n"
    def block(a: => String): String = {
      val save = indent
      indent += "  "
      try a finally indent = save
    }
    def pretty(e: Exp, env: List[String]): String = e match {
      case Lit(n) => n.toString
      case Sym(n) => "\""+n+"\""
      case Var(x) => env(x)
      case IsNum(a) => s"isNum(${pretty(a,env)})"
      case IsStr(a) => s"isStr(${pretty(a,env)})"
      case Lift(a) => s"lift(${pretty(a,env)})"
      case Fst(a) => s"${pretty(a,env)}._1"
      case Snd(a) => s"${pretty(a,env)}._2"
      case Equs(a,b) => s"${pretty(a,env)} == ${pretty(b,env)}"
      case Plus(a,b) => s"(${pretty(a,env)} + ${pretty(b,env)})"
      case Minus(a,b) => s"(${pretty(a,env)} - ${pretty(b,env)})"
      case Times(a,b) => s"(${pretty(a,env)} * ${pretty(b,env)})"
      case App(a,b) => s"(${pretty(a,env)} ${pretty(b,env)})"
      case Let(a,Var(n)) if n == env.length => pretty(a,env)
      case Let(a,b) => s"${indent}let x${env.length} = ${block(pretty(a,env))} in ${(pretty(b,env:+("x"+env.length)))}"
      case Lam(e) => s"${indent}fun f${env.length} x${env.length+1} ${block(pretty(e,env:+("f"+env.length):+("x"+(env.length+1))))}"
      case If(c,a,b) => s"${indent}if (${pretty(c,env)}) ${block(pretty(a,env))} ${indent}else ${block(pretty(b,env))}"
      case _ => e.toString
    }


    // ********************* test cases *********************

    val fac_exp = trans(fac_val,List("arg"))
    val eval_exp = trans(eval_val,List("arg","arg2"))
    val evalc_exp = trans(evalc_val,List("arg","arg2"))

    val fac_exp_anf = reify { anf(List(Sym("XX")),fac_exp) }
    val eval_exp_anf = reify { anf(List(Sym("XX"),Sym("XX")),eval_exp) }
    val evalc_exp_anf = reify { anf(List(Sym("XX"),Sym("XX")),evalc_exp) }

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


  def main(args: Array[String]) {
    testBasic()
    testAck1()
    testAck2()

    testFac1()
    testEval()

    println("done")
  }

}