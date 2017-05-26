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
    testDeltaEnv()
    testDelta()
    //testMutEval()
    //testMutInEval()
    testEvalSyntax()

    testMatches()
    testMatchesBis()

    //testUnstaging() // experimental

    println("done")
  }

}
