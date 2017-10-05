import org.scalameter._

import Base._
import Lisp._
import PinkBase._
import Pink._

object Bench {
  def bench(thunk: => Unit) = {    
    val time = measure {
      for (i <- 0 until 100000) {
        thunk
      }
    }
    time
  }

  def test() = {
    println("// ------- Bench.test --------")
    println("fac #,evaluated,compiled,traced evaluated,traced compiled")
    val oldLog = Base.log
    try {
      var counter = 0
      Base.log = {x => counter += 1 }
      val Code(fac_compiled) = ev(s"($evalc_src (quote $fac_src))")
      val Code(fac_traced_compiled) = ev(s"($trace_n_evalc_src (quote $fac_src))")
      val trace_n_eval_src = ev_nil(ev_nolift(evt_poly_src))
      val trace_n_eval_val = parseExp(trace_n_eval_src)
      val trace_n_eval_exp1 = trans(trace_n_eval_val, List("arg1"))

      for (i <- 0 until 10) {
        val t1 = bench(run { evalms(List(fac_val),App(App(eval_exp1,Var(0)),Lit(i))) })
        val t2 = bench(run { evalms(Nil,App(fac_compiled,Lit(i))) })
        val t3 = bench(run { evalms(List(fac_val),App(App(trace_n_eval_exp1,Var(0)),Lit(i))) })
        val t4 = bench(run { evalms(Nil,App(fac_traced_compiled,Lit(i))) })
        println(s"$i,$t1,$t2,$t3,$t4")
      }
    } finally {
      Base.log = oldLog
    }
  }
}
