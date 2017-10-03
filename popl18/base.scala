// multi-level core language λ↑↓ as a defitional interpreter in Scala

object Base {

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
  case class Cons(a:Exp,b:Exp) extends Exp
  case class Fst(a:Exp) extends Exp
  case class Snd(a:Exp) extends Exp
  case class IsNum(a:Exp) extends Exp
  case class IsStr(a:Exp) extends Exp
  case class IsCons(a:Exp) extends Exp
  case class Lift(e:Exp) extends Exp
  case class Run(b:Exp,e:Exp) extends Exp

  // for custom extensions to AST
  case class Special(f:Env => Val) extends Exp

  type Env = List[Val]

  abstract class Val
  case class Cst(n:Int) extends Val
  case class Str(s:String) extends Val
  case class Clo(env:Env,e:Exp) extends Val
  case class Tup(v1:Val,v2:Val) extends Val

  case class Code(e:Exp) extends Val

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
    case Cons(e1,e2) =>
      reflect(Cons(anf(env,e1),anf(env,e2)))
    case IsNum(e) =>
      reflect(IsNum(anf(env,e)))
    case IsStr(e) =>
      reflect(IsStr(anf(env,e)))
    case IsCons(e) =>
      reflect(IsCons(anf(env,e)))
    case Fst(e) =>
      reflect(Fst(anf(env,e)))
    case Snd(e) =>
      reflect(Snd(anf(env,e)))
    case Lift(e) =>
      reflect(Lift(anf(env,e)))
    case Run(b,e) =>
      reflect(Run(anf(env,b),reify(anf(env,e))))
    case Special(f) =>
      reflect(Special(f))
  }


  def reifyc(f: => Val) = reify { val Code(e) = f; e }
  def reflectc(s: Exp) = Code(reflect(s))

  def reifyv(f: => Val) = run {
    stBlock = Nil
    val res = f
    if (stBlock != Nil) {
      // if we are generating code at all,
      // the result must be code
      val Code(last) = res
      Code((stBlock foldRight last)(Let))
    } else {
      res
    }
  }

  // NBE-style 'reify' operator (semantics -> syntax)
  // lifting is shallow, i.e. 
  //   Rep[A]=>Rep[B]  ==> Rep[A=>B]
  //   (Rep[A],Rep[B]) ==> Rep[(A,B)]
  //   Cell[Rep[A]]    ==> Rep[Cell[A]]
  def lift(v: Val): Exp = v match {
    case Cst(n) => // number
      Lit(n)
    case Str(s) => // string
      Sym(s)
    case Tup(a,b) =>
      val (Code(u),Code(v)) = (a,b)
      reflect(Cons(u,v))
    case Clo(env2,e2) => // function
      stFun collectFirst { case (n,`env2`,`e2`) => n } match {
        case Some(n) =>
          Var(n)
        case None =>
          stFun :+= (stFresh,env2,e2)
          reflect(Lam(reify{ val Code(r) = evalms(env2:+Code(fresh()):+Code(fresh()),e2); r }))
      }
    case Code(e) => reflect(Lift(e))
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

    case Lift(e) => 
      Code(lift(evalms(env,e)))

    case Run(b,e) =>
      evalms(env,b) match {
        case Code(b1) =>
          reflectc(Run(b1, reifyc(evalms(env,e))))
        case _ =>
          val code = reifyc(evalms(env, e))
          reifyv(evalms(env, code))
      }

    case App(e1,e2) =>
      (evalms(env,e1), evalms(env,e2)) match {
        case (Clo(env3,e3), v2) => 
          evalms(env3:+Clo(env3,e3):+v2,e3)
        case (Code(s1), Code(s2)) =>
          Code(reflect(App(s1,s2)))
        case (r1, r2) =>
          throw new Exception(s"wrong app: ${r1.toString} ${r2.getClass}")
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
    case Cons(e1,e2) =>
      // introduction form, needs explicit lifting
      Tup(evalms(env,e1),evalms(env,e2))
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

    case IsCons(e1) =>
      (evalms(env,e1)) match {
        case (Code(s1)) =>
          Code(reflect(IsCons(s1)))
        case v => 
          Cst(if (v.isInstanceOf[Tup]) 1 else 0)
      }

    // special forms: custom eval, ...
    case Special(f) => f(env)
  }


  // pretty printing
  var indent = "\n"
  def block(a: => String): String = {
    val save = indent
    indent += "  "
    try a finally indent = save
  }
  def pretty(e: Exp, env: List[String]): String = e match {
    case Lit(n) => n.toString
    case Sym(n) => "\""+n+"\""
    case Var(x) => try env(x) catch { case _ => "?" }
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

  def check(a:Any)(s:String) = if (a.toString.trim != s.trim) {
    println("error: expected ")
    println("    "+s)
    println("but got")
    println("    "+a)
    (new AssertionError).printStackTrace
  }
}