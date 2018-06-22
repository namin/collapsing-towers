import Base._
import Lisp._
import Pink._
import parser._

/* WORK IN PROGRESS ON BYTECODE INTERPRETATION */

/*
+ 1) bytecode interpreter
+ 2) run factorial
+     loop + accumulator
-     extend to handle function calls (?)
- 3) stage-polymorphic bytecode interpreter
+     pure tracing
+     lift basic blocks as functions
-     memoization for recursion
- 4) extract fac code, dissolving bytecode level

- 5) metacircular evaluator
- 6) dissolve multiple interpretation levels
*/

/*
TODO: 
  - to support recursion, memory needs to 
    be dynamic

Questions:
  - what exactly should be dynamic?
      contents of memory
      entire memory, addresses, sp
      - 1) sp static, mem dynamic
      - 2) perhaps block becomes n nested functions where n = sp, each stack slot an arg?

  - PyPy paper has a register-based evaluator: 
    https://www3.hhu.de/stups/downloads/pdf/BoCuFiRi09_246.pdf

  - Glück's self-applicable online PE for flowchart has nested expressions
    https://pdfs.semanticscholar.org/8a49/462da3f61ad6c2fafc8bc884eff129958532.pdf  
*/


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

    run(s"""
    (let ex $exec_src
    (let prog (quote $test_src3)
    (let pc 'L0
    (let mem 'nil
    (let sp 1000
    ((((ex prog) pc) mem) sp))))))
    """)
    // expect 5

    run(s"""
    (let ex $exec_src
    (let prog (quote $test_src4)
    (let pc 'L0
    (let mem 'nil
    (let sp 1000
    ((((ex prog) pc) mem) sp))))))
    """)
    // expect 24

  }

  def testBasicTraceBC(): Unit = {
    println("// ------- test basic bytecode tracing (do not lift blocks) --------")
    
    def run(src: String) = {
      val prog_src = s"""(let exec-quote (lambda _ src (exec (trans-quote src))) $src)"""
      val prog_val = parseExp(prog_src)
      val prog_exp = trans(prog_val,Nil)
      val res = reifyv(evalms(Nil,prog_exp))
      res match {
        case Code(e) => println(pretty(e,Nil))
        case res => println(res)
      }
      res
    }

    run(s"""
    (let ex $exec_trace_src
    (let prog (quote $test_src1)
    (let pc 'L0
    (let mem 'nil
    (let sp 1000
    ((((ex prog) pc) mem) sp))))))
    """)
    // expect (2+3)

    run(s"""
    (let ex $exec_trace_src
    (let prog (quote $test_src2)
    (let pc 'L0
    (let mem 'nil
    (let sp 1000
    ((((ex prog) pc) mem) sp))))))
    """)
    // expect (2+3)

    run(s"""
    (let ex $exec_trace_src
    (let prog (quote $test_src3)
    (let pc 'L0
    (let mem 'nil
    (let sp 1000
    ((((ex prog) pc) mem) sp))))))
    """)
    // expect (if (2) (2 + 3) else (2 * 3))

/* NOTE: cannot trace loops/recursion (diverge)
    run(s"""
    (let ex $exec_comp_src
    (let prog (quote $test_src4)
    (let pc 'L0
    (let mem 'nil
    (let sp 1000
    ((((ex prog) pc) mem) sp))))))
    """)
    // expect ...
*/
  }

  def testBasicCompBC(): Unit = {
    println("// ------- test basic bytecode compilation --------")
    
    def run(src: String) = {
      val prog_src = s"""(let exec-quote (lambda _ src (exec (trans-quote src))) $src)"""
      val prog_val = parseExp(prog_src)
      val prog_exp = trans(prog_val,Nil)
      val res = reifyv(evalms(Nil,prog_exp))
      res match {
        case Code(e) => println(pretty(e,Nil))
        case res => println(res)
      }
      res
    }

    run(s"""
    (let ex $exec_comp_src
    (let prog (quote $test_src1)
    (let pc 'L0
    (let mem 'nil
    (let sp 1000
    ((((ex prog) pc) mem) sp))))))
    """)
    // expect let L0 = (\_. (2+3)) in (L0 _)

    run(s"""
    (let ex $exec_comp_src
    (let prog (quote $test_src2)
    (let pc 'L0
    (let mem 'nil
    (let sp 1000
    ((((ex prog) pc) mem) sp))))))
    """)
    // expect let L0 = (let L1 = (\_. (2+3)) in (L1 _)) in (L0 _)

    run(s"""
    (let ex $exec_comp_src
    (let prog (quote $test_src3)
    (let pc 'L0
    (let mem 'nil
    (let sp 1000
    ((((ex prog) pc) mem) sp))))))
    """)
    // expect let L0 = 
    //  if (2) (let L1 = (\_. (2+3)) in (L1 _))
    //  else   (let L2 = (\_. (2*3)) in (L2 _))
    // in (L0 _)
    // 
    // NOTE how functions becomes nested. We will have (a lot of) duplication
    // for control flow joins.

/* TODO: need to figure out memory story
    run(s"""
    (let ex $exec_comp_src
    (let prog (quote $test_src4)
    (let pc 'L0
    (let mem 'nil
    (let sp 1000
    ((((ex prog) pc) mem) sp))))))
    """)
    // expect ...
*/
  }


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

val test_src3 = commonReplace("""
(
  (L0 (
    (cst 2)
    (cst 3)
    (gets 1) ;; dup value 2
    (jif L1 L2)))
  (L1 (
    (+)
    (halt)))
  (L2 (
    (*)
    (halt)))
)
""")

// factorial (tail recursive and maintaining stack height)
val test_src4 = commonReplace("""
(
  (L0 (
    (cst 4)
    (cst 1)
    (jmp L1)))
  (L1 (;;loop(n,acc)
    (gets 1);; n
    (jif L2 L3)))
  (L2 (;;n != 0
    (gets 1);; n
    (cst 1)
    (-)
    (gets 1);; acc
    (gets 3);; n
    (*)
    (puts 2);; adjust stack height  n0 acc0 n1 acc1
    (puts 2)
    (jmp L1))) ;;loop(n-1,acc*n)
  (L3 (;;n == 0
    (halt))) ;;return acc
)
""")


/*
  Need: 
  - arithmetic stack
  - labels & jumps

  State:
  - program + pc
  - memory + sp
*/


val exec_poly_src = commonReplace("""
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
    (if (eq?  'cst    (car exp))    (((loop (cdr block)) (((update mem) sp) (maybe-lift (cadr exp)))) (+ sp 1))
    (if (eq?  'geta   (car exp))    (((loop (cdr block)) (((update mem) sp) (mem (cadr exp)))) (+ sp 1))
    (if (eq?  'gets   (car exp))    (((loop (cdr block)) (((update mem) sp) (mem (- (- sp 1) (cadr exp))))) (+ sp 1))
    (if (eq?  'puts   (car exp))    (((loop (cdr block)) (((update mem) (- (- sp 1) (cadr exp))) (mem (- sp 1)))) (- sp 1))
    (if (eq?  'drop   (car exp))    (((loop (cdr block)) mem) (- sp (cadr exp)))
    (if (eq?  '+      (car exp))    (((loop (cdr block)) (((update mem) (- sp 2)) (+ (mem (- sp 2)) (mem (- sp 1))))) (- sp 1))
    (if (eq?  '-      (car exp))    (((loop (cdr block)) (((update mem) (- sp 2)) (- (mem (- sp 2)) (mem (- sp 1))))) (- sp 1))
    (if (eq?  '*      (car exp))    (((loop (cdr block)) (((update mem) (- sp 2)) (* (mem (- sp 2)) (mem (- sp 1))))) (- sp 1))
    (if (eq?  '=      (car exp))    (((loop (cdr block)) (((update mem) (- sp 2)) (eq? (mem (- sp 2)) (mem (- sp 1))))) (- sp 1))
    (if (eq?  'halt   (car exp))    (mem (- sp 1))
    (if (eq?  'jmp    (car exp))    ((((exc prog) (cadr exp)) mem) sp)
    (if (eq?  'jif    (car exp))    (if (mem (- sp 1)) ((((exc prog) (cadr exp)) mem) (- sp 1)) ((((exc prog) (caddr exp)) mem) (- sp 1)))
    'eob)))))))))))))))) ;; failure, end of block
  ;;((find-block prog) pc)
  (let exc-block (maybe-lift-block (lambda _ _
    (((loop ((find-block prog) pc)) mem) sp)))
  (exc-block (maybe-lift-block '_))
  )))))))))
""")

val exec_src = exec_poly_src
                .replace("maybe-lift-block", "(lambda _ x x)")
                .replace("maybe-lift", "(lambda _ x x)")
val exec_trace_src = exec_poly_src
                .replace("maybe-lift-block", "(lambda _ x x)")
                .replace("maybe-lift", "lift")
val exec_comp_src = exec_poly_src
                .replace("maybe-lift-block", "lift")
                .replace("maybe-lift", "lift")

}