// A Lisp-Like Front-End

object Lisp {
  import Base._

  import scala.util.parsing.combinator._

  // s-expr parser
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

  def parseExp(s: String) = {
    val Success(v, _) = parseAll(exp, s)
    v
  }

  // ********************* convert exp encoded as val --> proper exp  *********************

  def trans(e: Val, env: List[String]): Exp = e match {
    case Cst(n) => Lit(n)
    case Str(s) => val i = env.lastIndexOf(s); assert(i>=0, s + " not in " + env); Var(i)
    case Tup(Str("quote"),  Tup(Str(s),N))   => Sym(s)
    case Tup(Str("+"),      Tup(a,Tup(b,N))) => Plus(trans(a,env),trans(b,env))
    case Tup(Str("-"),      Tup(a,Tup(b,N))) => Minus(trans(a,env),trans(b,env))
    case Tup(Str("*"),      Tup(a,Tup(b,N))) => Times(trans(a,env),trans(b,env))
    // (let x a b)
    case Tup(Str("let"),    Tup(Str(x),Tup(a,Tup(b,N)))) => Let(trans(a,env),trans(b,env:+x))
    // (lambda f x e)
    case Tup(Str("lambda"), Tup(Str(f),Tup(Str(x),Tup(e,N)))) => Lam(trans(e,env:+f:+x))
    case Tup(Str("if"),     Tup(c,Tup(a,Tup(b,N)))) => If(trans(c,env),trans(a,env),trans(b,env))
    case Tup(Str("num?"),   Tup(a,N)) => IsNum(trans(a,env))
    case Tup(Str("sym?"),   Tup(a,N)) => IsStr(trans(a,env))
    case Tup(Str("pair?"),  Tup(a,N)) => IsCons(trans(a,env))
    case Tup(Str("cons"),   Tup(a,Tup(b,N))) => Cons(trans(a,env),trans(b,env))
    case Tup(Str("car"),    Tup(a,N)) => Fst(trans(a,env))
    case Tup(Str("cdr"),    Tup(a,N)) => Snd(trans(a,env))
    case Tup(Str("cadr"),   Tup(a,N)) => Fst(Snd(trans(a,env)))
    case Tup(Str("caddr"),  Tup(a,N)) => Fst(Snd(Snd(trans(a,env))))
    case Tup(Str("cadddr"), Tup(a,N)) => Fst(Snd(Snd(Snd(trans(a,env)))))
    case Tup(Str("lift"),   Tup(a,N)) => Lift(trans(a,env))
    case Tup(Str("nolift"), Tup(a,N)) => trans(a,env)
    case Tup(Str("eq?"),    Tup(a,Tup(b,N))) => Equ(trans(a,env),trans(b,env))
    case Tup(Str("run"),    Tup(b,Tup(a,N))) => Run(trans(b,env),trans(a,env))
    case Tup(Str("log"),    Tup(b,Tup(a,N))) => Log(trans(b,env),trans(a,env))
    case Tup(Str("quote"),  Tup(a,N)) => Special(benv => a)
    case Tup(Str("trans"),  Tup(a,N)) =>
      Special(benv => Code(trans(evalms(benv, trans(a,env)), env)))
    case Tup(Str("lift-ref"),Tup(a,N)) =>
      Special(benv => Code(Special(b2 => evalms(benv,trans(a,env)))))
    case Tup(a,Tup(b,N)) => App(trans(a,env),trans(b,env))
  }

  def ev(src: String) = {
    val prog_src = src
    val prog_val = parseExp(prog_src)
    val prog_exp = trans(prog_val,Nil)
    reifyv(evalms(Nil,prog_exp))
  }
  def checkrun(src: String, dst: String) = {
    val res = ev(src)
    check(res)(dst)
    res
  }
  def checkcode(src: String, dst: String) = {
    val Code(res) = ev(src)
    check(pretty(res, Nil))(dst)
    res
  }
  def prettycode(e: Exp) = pretty(e, Nil)
  def checkrunlog(src: String, dst: String, expected_log: String) = {
    val oldLog = Base.log
    try {
      var s = ""
      Base.log = {x => s += x.toString+";" }
      val res = checkrun(src, dst)
      check(s)(expected_log)
      res
    } finally {
      Base.log = oldLog
    }
  }

  // basic test cases
  def test() = {
    println("// ------- Lisp.test --------")

    // Some aspects of our multi-stage language may appear 
    // a bit counterintuitive, but are essential for 
    // understanding how things work -- especially how
    // `lift` and `run` interact. 

    // Broadly we can do two things very easily:
    //  - Return code from the main program: (lift ...)
    //  - Build code and run it: (run 0 (.. (lift ..) ..))

    // The key thing to avoid is calling `run` on code
    // that is generated outside of the `run` statement.

    // Below are some concrete examples.

    // (1)

    // Below, operator `lift` will `reflect` its argument,
    // i.e. create a new binding Var(0) = Lam(Var(1))
    // in the current scope of expressions being generated. 
    // The present-stage variable `code` will be bound to 
    // expression Code(Var(0)). Whole-program evaluation
    // assembles all generated bindings into a nested let:
    checkrun(s"""
      (let code (lift (lambda f x x))
        code)
    ""","Code(Let(Lam(Var(1)),Var(0)))")

    // Pretty-printing hides the let if the expression 
    // is of the form (let x e x)
    checkcode(s"""
      (let code (lift (lambda f x x))
        code)
    ""","(lambda f0 x1 x1)")

    // So the result of evaluating the whole expression is
    // a block of code.
    // We can't ignore code that is reflected. For example,
    //   (let code (lift ..) 3)
    // Would throw an exception.

        
    // (2)

    // Things may get surprising if we try to generate 
    // and run code at the same time -- in general, one
    // needs to avoid running code that is generated
    // outside of the `run` statement.

    // Intuitively we might expect the following code to
    // return a plain closure (create a lifted closure, 
    // then eval it to a value).

    checkrun(s"""
      (let code (lift (lambda f x x))
        (run 0 code))
    ""","Code(Let(Lam(Var(1)),Var(0)))")


    // However, that's not what happens. Again, variable
    // `code` is bound to Code(Var(0)), the symbol generated
    // from reflecting the `(lift (lambda ...))`.
    // So `run` is called with Code(Var(0)), i.e. Var(0)
    // is the expression being evaluated, and that
    // happends to be exactly variable `code`, which is
    // again mapped to Code(Var(0)). Hence, the same
    // result as in (1).

    // Let's test our understanding further: 

    checkrun(s"""
      (let z (lift 42)
        (let code (lift (lambda f x x))
          (run 0 code)))
    ""","Code(Let(Lam(Var(1)),Lit(42)))")

    // Yes, this one returns 42, wrapped in a let that 
    // declares the lambda.

    // (Again, we have to use lift 42 instead of just 42, 
    // since we have to return a code value.)

    // Future versions may entirely prohibit such uses,
    // at the expense of additional checks that associate
    // a particular run-scope (or the top level) with
    // each Code value, and prevent mixing of levels.


    // (3)

    // Now how do we actually achieve the desired behavior:
    // declare a (closed) piece of code, then evaluate it?

    // Simple, we just wrap it in a function:

    checkrun(s"""
      (let code (lambda _ _ (lift (lambda f x x)))
        (run 0 (code 'dummy)))
    ""","Clo(List(Clo(List(),Lift(Lam(Var(3))))),Var(2))")

    // Disregarding the embedded closure environment that 
    // includes the value of `code`, the result can be 
    // read more conveniently as:
    //   Clo(code/Var0=..., (lambda f/Var1 x/Var2. x/Var))

    // The key is to ensure that all code pieces are reflected
    // within the **dynamic** scope of evaluating `run`'s
    // argument, including functions called within that
    // dynamic extent.


    // (4)

    // What if we want to run the same code multiple times
    // instead re-generating it? Simple, generate a function
    // and call it multiple times.

    // (simple exercise -- note that we're already generating 
    // functions)


    // (5)

    // Note that generated code can refer to present-stage
    // variables, using `quote` and `trans`.

    // This has a similar effect to standard quotation,
    // and comes with similar hygiene issues (some are
    // aggravated by our use of De Bruijn levels for 
    // variable names).

    checkrun(s"""
      (let z 21
        (let code (trans '(+ z z))
          (run 0 code)))
    ""","Cst(42)")

    // In contrast to `lift`, `trans` creates a closed 
    // code value directly.

    // Observe how the piece of code refers to variable
    // z = Var(0) directly:

    checkrun(s"""
      (let z 21
        (let code (trans '(+ z z))
          code))
    ""","Code(Plus(Var(0),Var(0)))")

    // Now let's take a look at the interaction with
    // bindings inside a `trans` block:

    checkrun(s"""
      (let z 21
        (let code (trans '(lambda _ x (+ z x)))
          code))
    ""","Code(Lam(Plus(Var(0),Var(2))))")

    // When we try to run this code, there's
    // again a problem:

    checkrun(s"""
      (let z 20
        (let code (trans '(lambda _ x (+ z x)))
          (let var2 10
            (let f (run 0 code)
              (f 22)))))
    ""","Cst(30)")

    // Intuitively we'd expect to get result 42,
    // but we obtain 30. This happens because 
    // `x` inside the `trans`ed lambda is
    // Var(2) at this position, but when `run`
    // is called, Var(2) actually corresponds
    // to `var2`.

    // A more elaborate representation of bound
    // and free names would fix this (e.g. locally
    // nameless) at the expense of complexity and
    // runtime overhead. Other hygiene issues  
    // (e.g. variables going out of scope) would 
    // remain.

    // Right now, the recommendation is to use
    // `trans` only as a direct argument to `run`:

    checkrun(s"""
      (let z 20
        (let var2 10
          (let f (run 0 (trans '(lambda _ x (+ z x))))
            (f 22))))
    ""","Cst(42)")

    // This is good enough for the key use case 
    // of `trans` in `EM` (see pink.scala).


    testDone()
  }
}
