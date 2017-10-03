#lang racket
(require redex)
(require "core.rkt")

(define iter-eval
  (lambda (e)
    (define (helper e i)
      (if (= (modulo i 50) 0)
          (display ".")
          'ok)
      (let ((r (apply-reduction-relation red e)))
        (let ((c (length r)))
          (if (= 1 c)
              (helper (car r) (+ i 1))
              (if (= 0 c)
                  e
                  r)))))
    (helper e 0)))

(define iter-eval-pp
  (lambda (e)
    (define (helper e i)
      (if (= (modulo i 100) 0)
          (begin (display e) (display "\n"))
          'ok)
      (let ((r (apply-reduction-relation red e)))
        (let ((c (length r)))
          (if (= 1 c)
              (helper (car r) (+ i 1))
              (if (= 0 c)
                  e
                  r)))))
    (helper e 0)))

(define acc-trace
  (lambda (e)
    (define (helper e a)
      (let ((r (apply-reduction-relation red e)))
        (let ((c (length r)))
          (if (= 1 c)
              (helper (car r) (cons (car r) a))
              (if (= 0 c)
                  (reverse a)
                  (reverse (cons (cons c r) a)))))))
    (helper e (cons e '()))))

(define pp-each
  (lambda (l)
    (if (null? l) (display "done\n") (begin (display (car l)) (display "\n") (pp-each (cdr l))))))

(define pp-fl
  (lambda (l)
    (pp-each (list (car l) (last l)))))

(define fac
  `(app l (lam fac n
   (if n
       (times n (app fac (minus n (app l (lit 1)))))
       (app l (lit 1))))))

(pp-each (acc-trace (term (app (let l (lam f x x) ,fac) (lit 3)))))
(pp-each (acc-trace (second (last (acc-trace (term (app (let l (lam f x (lift x)) ,fac) (lift (lit 3)))))))))

(define evl (lambda (l)
  `(fix (lam ev (lam exp (lam env
   (if (isLit exp) ,(l `exp)
   (if (isStr exp) (app env exp)
   (if (eq (str "quote") (car exp)) ,(l `(car (cdr exp)))
   (if (eq (str "plus")  (car exp)) (plus  (app (app ev (car (cdr exp))) env) (app (app ev (car (cdr (cdr exp)))) env))
   (if (eq (str "minus") (car exp)) (minus (app (app ev (car (cdr exp))) env) (app (app ev (car (cdr (cdr exp)))) env))
   (if (eq (str "times") (car exp)) (times (app (app ev (car (cdr exp))) env) (app (app ev (car (cdr (cdr exp)))) env))
   (if (eq (str "eq")    (car exp)) (eq    (app (app ev (car (cdr exp))) env) (app (app ev (car (cdr (cdr exp)))) env))
   (if (eq (str "if")    (car exp)) (if (app (app ev (car (cdr exp))) env) (app (app ev (car (cdr (cdr exp)))) env) (app (app ev (car (cdr (cdr (cdr exp))))) env))
   (if (eq (str "lam")   (car exp)) ,(l `(lam f x (app (app ev (car (cdr (cdr (cdr exp))))) (lam y (if (eq y (car (cdr exp))) f (if (eq y (car (cdr (cdr exp)))) x (app env y)))))))
   (if (eq (str "let")   (car exp)) (let x (app (app ev (car (cdr (cdr exp)))) env) (app (app ev (car (cdr (cdr (cdr exp))))) (lam y (if (eq y (car (cdr exp))) x (app env y)))))
   (if (eq (str "lift")  (car exp)) (lift  (app (app ev (car (cdr exp))) env))
   (if (eq (str "isLit") (car exp)) (isLit (app (app ev (car (cdr exp))) env))
   (if (eq (str "isStr") (car exp)) (isStr (app (app ev (car (cdr exp))) env))
   (if (eq (str "cons")  (car exp)) ,(l `(cons  (app (app ev (car (cdr exp))) env) (app (app ev (car (cdr (cdr exp)))) env)))
   (if (eq (str "car")   (car exp)) (car (app (app ev (car (cdr exp))) env))
   (if (eq (str "cdr")   (car exp)) (cdr (app (app ev (car (cdr exp))) env))
   (if (eq (str "app")   (car exp)) (app (app (app ev (car (cdr exp))) env) (app (app ev (car (cdr (cdr exp)))) env))
   (str "error")
   )))))))))))))))))))))))

(define ev (evl (lambda (x) `(app l ,x))))

(pp-each (acc-trace (term (app (app (let l (lam x x) ,ev) (lit 3)) (lam y y)))))
(pp-each (acc-trace (term (app (app (let l (lam x (lift x)) ,ev) (lit 3)) (lam y y)))))

(define quotify
  (lambda (e)
    (if (or (not (pair? e)) (eq? (car e) 'lit) (eq? (car e) 'str) (eq? (car e) 'code))
        (if (symbol? e) (list 'str (symbol->string e)) (if (null? e) (list 'str "nil")
        (if (eq? (car e) 'str) (list 'cons '(str "quote") (list 'cons e (list 'str "nil"))) e)))
        (list 'cons (quotify (car e)) (quotify (cdr e))))))

(define facl (lambda (l)
  `(fix ,(l `(lam fac ,(l `(lam n
   (if n
       (times n (app fac (minus n ,(l `(lit 1)))))
       ,(l `(lit 1))))))))))

(define fibl (lambda (l)
  `(fix ,(l `(lam fib ,(l `(lam n
   (if n
       (if (minus n ,(l `(lit 1)))
           ,(l `(lit 1))
           (plus (app fib (minus n ,(l `(lit 1)))) (app fib (minus n ,(l `(lit 2))))))
       ,(l `(lit 0))))))))))

(pp-each (acc-trace (term ,(fibl (lambda (x) `(lift ,x))))))
(length (acc-trace (term (app (app ,(evl (lambda (x) `(lift ,x))) ,(quotify (fibl (lambda (x) x)))) (lam y y)))))
(define r (acc-trace (term (app (app ,(evl (lambda (x) `(lift ,x))) ,(quotify (fibl (lambda (x) x)))) (lam y y)))))

(define fl (lambda (l)
  `(fix ,(l `(lam ev ,(l `(lam n ,(l `(lam _
   (if n
       (times n (app (app ev (minus n ,(l `(lit 1)))) ,(l `(lit 0))))
       ,(l `(lit 1))))))))))))

(define r2 (acc-trace (term (app (app ,(evl (lambda (x) `(lift ,x))) ,(quotify (fl (lambda (x) x)))) (lam y y)))))

(pp-fl (acc-trace (term (app (app (let l (lam x x) ,ev) ,(quotify '(times (plus (lit 1) (lit 2)) (lit 4)))) (lam y y)))))
(pp-fl (acc-trace (term (app (app (let l (lam x (lift x)) ,ev) ,(quotify '(times (plus (lit 1) (lit 2)) (lit 4)))) (lam y y)))))
(pp-fl (acc-trace (term (app (app (let l (lam x x) ,ev) ,(quotify '(app (lam x (times x x)) (lit 3)))) (lam y y)))))
(pp-fl (acc-trace (term (app (app (let l (lam x (lift x)) ,ev) ,(quotify '(lam x (times x x)))) (lam y y)))))
(pp-fl (acc-trace (term (app (app (let l (lam x x) ,ev) ,(quotify `(if (lit 1) (lit 1) (lit 0)))) (lam y y)))))
(pp-fl (acc-trace (term (app (app (let l (lam x x) ,ev) ,(quotify `(app (lam x (if x (lit 1) (lit 0))) (lit 3)))) (lam y y)))))
(length (acc-trace (term (app (app (let l (lam x x) ,ev) ,(quotify `(app ,(facl (lambda (x) x)) (lit 3)))) (lam y y)))))
(length (acc-trace (term (app (app ,(evl (lambda (x) x)) ,(quotify `(app ,(facl (lambda (x) x)) (lit 3)))) (lam y y)))))
(length (acc-trace (term (app (app (let l (lam x x) ,ev) ,(quotify `(app (let l (lam x x) ,(facl (lambda (x) x))) (lit 3)))) (lam y y)))))
(length (acc-trace (term (app (app (let l (lam x x) ,ev) ,(quotify `(app (let l (lam x x) ,fac) (lit 3)))) (lam y y)))))
(length (acc-trace (term (app (app ,(evl (lambda (x) x)) ,(quotify `(app (let l (lam x x) ,fac) (lit 3)))) (lam y y)))))
(pp-fl (acc-trace (term (app (app (let l (lam x (lift x)) ,ev) ,(quotify (facl (lambda (x) x)))) (lam y y)))))
(pp-fl (acc-trace `(app
                    ,(second (last (acc-trace (term (app (app ,(evl (lambda (x) `(lift ,x))) ,(quotify (facl (lambda (x) x)))) (lam y y))))))
                    (lit 3))))
(define o
  (iter-eval `(app (app ,(evl (lambda (x) `(lift ,x))) ,(quotify (evl (lambda (x) x)))) (lam y y)))
)
(pp-fl (acc-trace `(app (app
,(second o)
,(quotify '(app (lam x (plus x x)) (lit 3)))) (lam y y))))
(last (acc-trace (term (app (app ,(evl (lambda (x) x)) ,(quotify `(app (app ,(evl (lambda (x) x)) (lit 3)) (lam y y)))) (lam y y)))))
(last (acc-trace (term (app (app ,(evl (lambda (x) x)) ,(quotify `(app (app ,(evl (lambda (x) `(lift ,x))) (lit 3)) (lam y y)))) (lam y y)))))
(last (acc-trace (term (app (app ,(evl (lambda (x) x)) ,(quotify `(app (app ,(evl (lambda (x) x)) (app (lam x x) (lit 3))) (lam y y)))) (lam y y)))))
(last (acc-trace (term (app (app ,(evl (lambda (x) x)) ,(quotify `(app (app ,(evl (lambda (x) `(lift ,x))) (app (lam x x) (lit 3))) (lam y y)))) (lam y y)))))
(last (acc-trace (term (app (app ,(evl (lambda (x) x)) ,(quotify `(app (app ,(evl (lambda (x) `(lift ,x))) (lam x x)) (lam y y)))) (lam y y)))))
(last (acc-trace (term (app (app ,(evl (lambda (x) `(lift ,x))) ,(quotify '(lam exp (eq (str "foo") (car exp))))) (lam y y)))))

(pp-each (acc-trace (term (reflect (code (plus (lit 1) (lit 2)))))))
(pp-each (acc-trace (term (lift (plus (lit 1) (lit 2))))))
(pp-each (acc-trace (term (app (lam x x) (lit 2)))))
(pp-each (acc-trace (term (lift (app (lam x x) (lit 2))))))
(pp-each (acc-trace (term (lift (lam x x)))))
(pp-each (acc-trace (term (lift (if (lit 0) (lit 1) (plus (lit 1) (lit 2)))))))
(pp-each (acc-trace (term (if (lit 0) (lift (plus (lit 3) (lit 1))) (plus (lift (lit 1)) (lift (lit 2)))))))
(pp-each (acc-trace (term (plus (lift (lit 0)) (plus (lift (lit 1)) (lift (plus (lit 2) (lit 3))))))))
(pp-each (acc-trace (term (plus (plus (lift (lit 0)) (lift (lit 1))) (plus (lift (lit 2)) (lift (lit 3)))))))


(pp-each (acc-trace (term (app (app
  (lam fun
       (app
        (lam F
             (app F F))
        (lam F
             (app fun (lam x (app (app F F) x))))))
  (lam fac
       (lam n
            (if n
                (times n (app fac (minus n (lit 1))))
                (lit 1)))))
  (lit 6)))))

(pp-each (acc-trace (term (app (fix
  (lam fac
       (lam n
            (if n
                (times n (app fac (minus n (lit 1))))
                (lit 1)))))
  (lit 6)))))

(pp-each (acc-trace (term (lift (lam x (lift (plus (lit 1) (lit 2))))))))

(pp-each (acc-trace (term (lift (lam x (plus x (lift (plus (lit 1) (lit 2)))))))))

(pp-each (acc-trace (term (app (lift (lam x (lift (plus (lit 1) (lit 2))))) (lift (lit 2))))))

(pp-each (acc-trace (term (plus (lift (if (lit 0) (lit 1) (lit 2))) (if (lift (lit 0)) (lift (lit 1)) (lift (lit 2)))))))

(pp-each (acc-trace (term (run (code (lit 1)) (code (plus (lit 1) (lit 2)))))))

(pp-each (acc-trace (term (run (lit 1) (code (plus (lit 1) (lit 2)))))))

(pp-each (acc-trace (term (plus (app (lift (lam x x)) (lift (lit 1))) (lift (lit 2))))))

(pp-each (acc-trace (term (lift (lam x (plus (plus (lift (lit 1)) (lift (lit 2))) (lift (lit 3))))))))

(pp-each (acc-trace (term (app (lift (lam x (plus (plus (lift (lit 1)) (lift (lit 2))) (lift (lit 3))))) (if (lift (lit 0)) (lift (lit 1)) (lift (lit 2)))))))

(pp-each (acc-trace (term (lift (lam fac (lift (lam n
            (if n
                (times n (app fac (minus n (lift (lit 1)))))
                (lift (lit 1))))))))))

(pp-each (acc-trace (term (fix (lift (lam fac (lift (lam n
            (if n
                (times n (app fac (minus n (lift (lit 1)))))
                (lift (lit 1)))))))))))

(pp-each (acc-trace (term (app
 (let x4 (lam fac (let x3 (lam n1 (let x2 (if n1 (let x (minus n1 (lit 1)) (let x1 (app fac x) (let x (times n1 x1) x))) (lit 1)) x2)) x3)) (let x (fix x4) x))
 (lit 6)))))

(display "Fig. 3. Example of small-step derivation\n")
(pp-each (acc-trace (term (lift (lam _ x (plus x (times x x)))))))