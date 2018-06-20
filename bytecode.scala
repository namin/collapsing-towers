import Base._
import Lisp._
import Pink._
import parser._

/* WORK IN PROGRESS ON BYTECODE INTERPRETATION */

object Bytecode {

  def testBasicBC(): Unit = {
    println("// ------- test basic bytecode eval --------")
    
    def run(src: String) = {
      val prog_src = s"""(let exec-quote (lambda _ src (exec (trans-quote src))) $src)"""
      val prog_val = parseExp(prog_src)
      val prog_exp = trans(prog_val,Nil)
      val res = reifyv(evalms(Nil,prog_exp))
      println(res)
      res
    }

    run(s"""
    (let ex $exec_src
    (let prog (quote $test_src1)
    (let pc 'L0
    (let mem 'nil
    (let sp 1000
    ((((ex prog) pc) mem) sp))))))
    """)
    // expect 5

    run(s"""
    (let ex $exec_src
    (let prog (quote $test_src2)
    (let pc 'L0
    (let mem 'nil
    (let sp 1000
    ((((ex prog) pc) mem) sp))))))
    """)
    // expect 5



  }

/*
  Need: 
  - arithmetic stack
  - labels & jumps

  State:
  - pc
  - stack
*/


val test_src1 = commonReplace("""
(
  (L0 (
    (cst 2)
    (cst 3)
    (+)
    (halt)))
)
""")

val test_src2 = commonReplace("""
(
  (L0 (
    (cst 2)
    (cst 3)
    (jmp L1)))
  (L1 (
    (+)
    (halt)))
)
""")

val exec_src = commonReplace("""
(lambda exc prog (lambda _ pc (lambda _ mem (lambda _ sp
  ;; generic list lookup: find (eq? a) (a b) = a
  (let find (lambda find p (lambda _ xs
    (if (pair? xs)
      (if (p (car xs)) (car xs) ((find p) (cdr xs)))
      'nil)))
  ;; find block in program: find-block 'L0 '((L0 as) (L1 bs)) = as
  (let find-block (lambda _ prog (lambda _ label
    (car (cdr ((find (lambda _ lb (eq? label (car lb)))) prog)))))
  ;; generic function update: fun[i -> x]
  (let update (lambda _ fun (lambda _ i (lambda _ x
    (lambda _ j (if (eq? i j) x (fun j))))))
  ;; exec basic block, e.g. ((cst 0) (+) (jmp L1))
  (let loop (lambda loop block (lambda _ mem (lambda _ sp
    (let exp (car block)
    (if (eq?  'cst    (car exp))    (((loop (cdr block)) (((update mem) sp) (cadr exp))) (+ sp 1))
    (if (eq?  '+      (car exp))    (((loop (cdr block)) (((update mem) (- sp 2)) (+ (mem (- sp 2)) (mem (- sp 1))))) (- sp 1))
    (if (eq?  'halt   (car exp))    (mem (- sp 1))
    (if (eq?  'jmp    (car exp))    ((((exc prog) (cadr exp)) mem) sp)
    'eob)))))))) ;; failure, end of block
  ;;((find-block prog) pc)
  (((loop ((find-block prog) pc)) mem) sp)
  ))))))))
""")







/*
  i = 0
  while (i < n) {
    i = i + 1
  }
  return i

L0:
  (const 0)
  (write i)
L1:
  (read i)
  (read n)
  (<)
  (not)
  (jnz L2)
  (read i)
  (const 1)
  (+)
  (write i)
  (jmp L1)
L2:
  (read i)
  (halt)
*/


  def testFacBC(): Unit = {
    
  }

}