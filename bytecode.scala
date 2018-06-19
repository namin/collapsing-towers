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
    (let prog (lambda _ _ (quote $test_src1));; ignore label atm
    (let pc 'L0
    (let mem 'nil
    (let sp 1000
    (((((ex ex) prog) pc) mem) sp))))))
    """)

  }

/*
  Need: 
  - arithmetic stack
  - labels & jumps

  State:
  - pc
  - stack
*/


val exec_src = commonReplace("""
(lambda _ exec (lambda _ prog (lambda _ pc (lambda _ mem (lambda _ sp
  (let update (lambda _ fun (lambda _ i (lambda _ x
    (lambda _ j (if (eq? i j) x (fun j))))))
  ;; e.g. ((cst 0) (+) (jmp L1))
  (let loop (lambda loop exp (lambda _ mem (lambda _ sp
    (if (eq?  'cst    (caar exp))    (((loop (cdr exp)) (((update mem) sp) (cadar exp))) (+ sp 1))
    (if (eq?  '+      (caar exp))    (((loop (cdr exp)) (((update mem) (- sp 2)) (+ (mem (- sp 2)) (mem (- sp 1))))) (- sp 1))
    (if (eq?  'halt   (caar exp))    (mem (- sp 1))
    'eof))))))
  (((loop (prog pc)) mem) sp))))))))
""")

/*
  (if (num?                exp)    (maybe-lift exp)
  (if (sym?                exp)    (env exp)
  (if (sym?           (car exp))   
    (if (eq?  '+      (car exp))   (+   ((eval (cadr exp)) env) ((eval (caddr exp)) env))
    (if (eq?  '-      (car exp))   (-   ((eval (cadr exp)) env) ((eval (caddr exp)) env))
    (if (eq?  '*      (car exp))   (*   ((eval (cadr exp)) env) ((eval (caddr exp)) env))
    (if (eq?  'eq?    (car exp))   (eq? ((eval (cadr exp)) env) ((eval (caddr exp)) env))
    (if (eq?  'if     (car exp))   (if  ((eval (cadr exp)) env) ((eval (caddr exp)) env) ((eval (cadddr exp)) env))
    (if (eq?  'lambda (car exp))   (maybe-lift (lambda f x ((eval (cadddr exp)) 
      (lambda _ y (if (eq? y (cadr exp)) f (if (eq? y (caddr exp)) x (env y)))))))
    (if (eq?  'let    (car exp))   (let x ((eval (caddr exp)) env) ((eval (cadddr exp))
      (lambda _ y (if (eq?  y (cadr exp)) x (env y)))))
    (if (eq?  'lift   (car exp))   (lift ((eval (cadr exp)) env))
    (if (eq?  'num?   (car exp))   (num? ((eval (cadr exp)) env))
    (if (eq?  'sym?   (car exp))   (sym? ((eval (cadr exp)) env))
    (if (eq?  'car    (car exp))   (car  ((eval (cadr exp)) env))
    (if (eq?  'cdr    (car exp))   (cdr  ((eval (cadr exp)) env))
    (if (eq?  'cons   (car exp))   (maybe-lift (cons ((eval (cadr exp)) env) ((eval (caddr exp)) env)))
    (if (eq?  'quote  (car exp))   (maybe-lift (cadr exp))
    (if (eq?  'pair?  (car exp))   (pair? ((eval (cadr exp)) env))
    (if (eq?  'code?  (car exp))   (code? ((eval (cadr exp)) env) ((eval (caddr exp)) env))
    (if (equs 'refNew (car exp))      (maybe-lift (refNew ((eval (cadr exp)) env)))
    (if (equs 'refRead (car exp))     (refRead ((eval (cadr exp)) env))
    (if (equs 'refWrite (car exp))    (refWrite ((eval (cadr exp)) env) ((eval (caddr exp)) env))
    ((env (car exp)) ((eval (cadr exp)) env)))))))))))))))))))))
  (((eval (car exp)) env) ((eval (cadr exp)) env)))))))))
""")
*/

val test_src1 = commonReplace("""
(
  (cst 2)
  (cst 3)
  (+)
  (halt)
)
""")

val test_src2 = commonReplace("""
(L0 (
  (cst 2)
  (cst 3)
  (+)
  (halt)
))
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



  val dec_src = """
  while (i < n) {
    i = i + 1
  }
  return i
  """



  val fac_src = """
  ()
  """

  def testFacBC(): Unit = {
    
  }

}