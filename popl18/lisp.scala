// A Lisp-Like Front-End

object Lisp {
  import Base._

  import scala.util.parsing.combinator._

  // adapted from github.com/namin/lms-black
  object parser extends JavaTokenParsers with PackratParsers {
    override val whiteSpace = """(\s|(;[^\n]*))+""".r

    def S(x:String) = Str(x)
    def P(x:Val,y:Val) = Tup(x,y)
    def I(x:Int) = Cst(x)
    val N = Str(".")

    lazy val exp: Parser[Val] =
        wholeNumber ^^ { case s => I(s.toInt) } |
        """[^\s\(\)'"]+""".r ^^ { case s => S(s) } |
        "'" ~> exp ^^ { case s => P(S("quote"), P(s, N)) } |
        "()" ^^ { case _ => N } |
        "(" ~> exps <~ ")" ^^ { case vs => vs }

    lazy val exps: Parser[Val] =
        exp ~ opt(exps) ^^ { case v~Some(vs) => P(v, vs) case v~None => P(v,N) }
  }

  import parser._

  // ********************* convert exp encoded as val --> exp  *********************

  def trans(e: Val, env: List[String]): Exp = e match {
    case Cst(n) => Lit(n)
    case Str(s) => val i = env.lastIndexOf(s); assert(i>=0, s + " not in " + env); Var(i)
    case Tup(Str("quote"),Tup(Str(s),N)) => Sym(s)
    case Tup(Str("+"),Tup(a,Tup(b,N))) => Plus(trans(a,env),trans(b,env))
    case Tup(Str("-"),Tup(a,Tup(b,N))) => Minus(trans(a,env),trans(b,env))
    case Tup(Str("*"),Tup(a,Tup(b,N))) => Times(trans(a,env),trans(b,env))
    // (let x a b)
    case Tup(Str("let"),Tup(Str(x),Tup(a,Tup(b,N)))) => Let(trans(a,env),trans(b,env:+x))
    // (lambda f x e)
    case Tup(Str("lambda"),Tup(Str(f),Tup(Str(x),Tup(e,N)))) => Lam(trans(e,env:+f:+x))
    case Tup(Str("if"),Tup(c,Tup(a,Tup(b,N)))) => If(trans(c,env),trans(a,env),trans(b,env))
    case Tup(Str("num?"),Tup(a,N)) => IsNum(trans(a,env))
    case Tup(Str("sym?"),Tup(a,N)) => IsStr(trans(a,env))
    case Tup(Str("pair?"),Tup(a,N)) => IsCons(trans(a,env))
    case Tup(Str("cons"),Tup(a,Tup(b,N))) => Cons(trans(a,env),trans(b,env))
    case Tup(Str("car"),Tup(a,N)) => Fst(trans(a,env))
    case Tup(Str("cdr"),Tup(a,N)) => Snd(trans(a,env))
    case Tup(Str("cadr"),Tup(a,N)) => Fst(Snd(trans(a,env)))
    case Tup(Str("caddr"),Tup(a,N)) => Fst(Snd(Snd(trans(a,env))))
    case Tup(Str("cadddr"),Tup(a,N)) => Fst(Snd(Snd(Snd(trans(a,env)))))
    case Tup(Str("lift"),Tup(a,N)) => Lift(trans(a,env))
    case Tup(Str("nolift"),Tup(a,N)) => trans(a,env)
    case Tup(Str("eq?"),Tup(a,Tup(b,N))) => Equs(trans(a,env),trans(b,env))
    case Tup(Str("run"),Tup(b,Tup(a,N))) => Run(trans(b,env),trans(a,env))
    case Tup(Str("quote"),Tup(a,N)) => Special(benv => a)
    // default case: generic app
    case Tup(a,Tup(b,N)) => App(trans(a,env),trans(b,env))
  }

  def parseExp(s: String) = {
    val Success(v, _) = parseAll(exp, s)
    v
  }
}
