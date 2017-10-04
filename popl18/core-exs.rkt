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

(define evl (lambda (l)
  `(lam ev exp (lam _ env
   (if (isLit exp) ,(l `exp)
   (if (isStr exp) (app env exp)
   (if (eq (str "quote") (car exp)) ,(l `(car (cdr exp)))
   (if (eq (str "plus")  (car exp)) (plus  (app (app ev (car (cdr exp))) env) (app (app ev (car (cdr (cdr exp)))) env))
   (if (eq (str "minus") (car exp)) (minus (app (app ev (car (cdr exp))) env) (app (app ev (car (cdr (cdr exp)))) env))
   (if (eq (str "times") (car exp)) (times (app (app ev (car (cdr exp))) env) (app (app ev (car (cdr (cdr exp)))) env))
   (if (eq (str "eq")    (car exp)) (eq    (app (app ev (car (cdr exp))) env) (app (app ev (car (cdr (cdr exp)))) env))
   (if (eq (str "if")    (car exp)) (if (app (app ev (car (cdr exp))) env) (app (app ev (car (cdr (cdr exp)))) env) (app (app ev (car (cdr (cdr (cdr exp))))) env))
   (if (eq (str "lam")   (car exp)) ,(l `(lam f x (app (app ev (car (cdr (cdr (cdr exp))))) (lam _ y (if (eq y (car (cdr exp))) f (if (eq y (car (cdr (cdr exp)))) x (app env y)))))))
   (if (eq (str "let")   (car exp)) (let x (app (app ev (car (cdr (cdr exp)))) env) (app (app ev (car (cdr (cdr (cdr exp))))) (lam _ y (if (eq y (car (cdr exp))) x (app env y)))))
   (if (eq (str "lift")  (car exp)) (lift  (app (app ev (car (cdr exp))) env))
   (if (eq (str "isLit") (car exp)) (isLit (app (app ev (car (cdr exp))) env))
   (if (eq (str "isStr") (car exp)) (isStr (app (app ev (car (cdr exp))) env))
   (if (eq (str "cons")  (car exp)) ,(l `(cons  (app (app ev (car (cdr exp))) env) (app (app ev (car (cdr (cdr exp)))) env)))
   (if (eq (str "car")   (car exp)) (car (app (app ev (car (cdr exp))) env))
   (if (eq (str "cdr")   (car exp)) (cdr (app (app ev (car (cdr exp))) env))
   (if (eq (str "app")   (car exp)) (app (app (app ev (car (cdr exp))) env) (app (app ev (car (cdr (cdr exp)))) env))
   (str "error")
   )))))))))))))))))))))

(define quotify
  (lambda (e)
    (if (or (not (pair? e)) (eq? (car e) 'lit) (eq? (car e) 'str) (eq? (car e) 'code))
        (if (symbol? e) (list 'str (symbol->string e)) (if (null? e) (list 'str "nil")
        (if (eq? (car e) 'str) (list 'cons '(str "quote") (list 'cons e (list 'str "nil"))) e)))
        (list 'cons (quotify (car e)) (quotify (cdr e))))))

(define facl (lambda (l)
`(lam fac n
   (if n
       (times n (app fac (minus n ,(l `(lit 1)))))
       ,(l `(lit 1))))))


(test-equal (iter-eval (term (app ,(facl (lambda (x) x)) (lit 3)))) (term (lit 6)))
(test-equal (iter-eval (term (app (app ,(evl (lambda (x) x)) (lit 3)) (lam _ y y)))) (term (lit 3)))
(test-equal (iter-eval (term (app (app ,(evl (lambda (x) x)) ,(quotify (term (lit 3)))) (lam _ y y)))) (term (lit 3)))
(test-equal (iter-eval (term (app (app ,(evl (lambda (x) x)) ,(quotify (term (plus (lit 1) (lit 2))))) (lam _ y y)))) (term (lit 3)))
(test-equal (iter-eval (term (app (app ,(evl (lambda (x) x)) ,(quotify (term (app (lam _ x (plus (lit 1) x)) (lit 2))))) (lam _ y y)))) (term (lit 3)))
;(iter-eval (term (app (app ,(evl (lambda (x) `(lift ,x))) ,(quotify (term (lam _ x (plus (lit 1) x))))) (lam _ y y))))
(test-equal (iter-eval (term (app (run (lit 0) (app (app ,(evl (lambda (x) `(lift ,x))) ,(quotify (term (lam _ x (plus (lit 1) x))))) (lam _ y y))) (lit 2)))) (term (lit 3)))
;(iter-eval (term (app (run (lift (lit 0)) (app (app ,(evl (lambda (x) `(lift ,x))) ,(quotify (term (lam _ x (plus (lit 1) x))))) (lam _ y y))) (lit 2))))
(test-equal (iter-eval (term (app (run (lit 0) (app (app ,(evl (lambda (x) `(lift ,x))) ,(quotify (facl (lambda (x) x)))) (lam _ y y))) (lit 3)))) (term (lit 6)))

(display "\n")
(display "Fig. 3. Example of small-step derivation\n")
(pp-each (acc-trace (term (lift (lam _ x (plus x (times x x)))))))