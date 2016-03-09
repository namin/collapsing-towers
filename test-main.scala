object TestMain {
  import Base._
  import Lisp._
  def main(args: Array[String]) {
    testBasic()
    testAck1()
    testAck2()

    testFac1()
    testEval()

    println("done")
  }

}