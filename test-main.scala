object TestMain {
  import Base._
  import Lisp._
  import Matches._
  def main(args: Array[String]) {
    testBasic()
    testAck1()
    testAck2()

    testFac1()
    testEval()
    testEvalCps()
    testEvalAmb()
    testDeltaEnv()
    testDelta()
    //testMutEval()
    //testMutInEval()
    testEvalSyntax()

    testMatches()
    testMatchesBis()

    //testUnstaging() // experimental

    //println("done with tests")
    //println("")
    //println("PINK BENCHMARKS")
    //benchFac()
    //TODO:benchMatches()

    Pink.test()
    Pink_clambda.test()
    Pink_CPS.test()
    Pink_macro.test()
  }

}
