object TestMain {
  def main(args: Array[String]) {
    PE.test()
    Base.test()
    Lisp.test()
    Pink.test()
    Pink_CPS.test()
    Pink_clambda.test()
    Matcher.test()
    //Bench.test()
    println("DONE")
  }
}
