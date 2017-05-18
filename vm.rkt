#lang racket
(require redex)

(define-language vm
  (e x (lit number) (lam x e) (cons e e) (code e) (let x e e) (app e e) (if e e e) (b e e) (fix e) (lift e) (run e e))
  (g (reflect e) (reify e) e)
  (v (lit number) (lam x e) (cons v v) (code e))
  (b plus minus times)
  (E hole (cons E e) (cons v E) (let x E g) (if E e e) (b E e) (b v E) (fix E e) (lift E) (run E e))
  (R hole (lift (lam x R)) (if (code e) R g) (if (code e) v R) (run (code e) R) (let x R g) (let x v R))
  (x (variable-except lit lam cons let app if plus minus times fix lift run reflect reify pair code)))

(define not-code? (lambda (x) (not ((redex-match vm (code e)) x))))

(define red
  (reduction-relation
   vm
   (--> (in-hole E (let x v e))                 (in-hole E (subst x v e)) "let")
   (--> (in-hole E (app (lam x e) v))               (in-hole E (subst x v e)) "lam")
   (--> (in-hole E (if (lit 0) e_1 e_2))        (in-hole E e_2)           "if0")
   (--> (in-hole E (if (lit number_1) e_1 e_2)) (in-hole E e_1)           "ifn"
        (side-condition (not (= 0 (term number_1)))))
   (--> (in-hole E (plus (lit number_1) (lit number_2)))
        (in-hole E (lit ,(+ (term number_1) (term number_2))))             "plus")
   (--> (in-hole E (minus (lit number_1) (lit number_2)))
        (in-hole E (lit ,(- (term number_1) (term number_2))))             "minus")
   (--> (in-hole E (times (lit number_1) (lit number_2)))
        (in-hole E (lit ,(* (term number_1) (term number_2))))             "times")
   (--> (in-hole E (fix (lam x e))) (in-hole E (subst x (fix (lam x e)) e)) "fix")
   (--> (in-hole E (cons v_1 v_2))  (in-hole E (pair v_1 v_2))            "cons")
   (--> (in-hole E (if (code e_0) (code e_1) (code e_2)))
        (in-hole E (reflect (if (code e_0) e_1 e_2)))                     "ifccc")
   (--> (in-hole E (if (code e_0) e_1 e_2))
        (in-hole E (if (code e_0) (reify e_1) (reify e_2)))               "ifc"
        (side-condition (and (not-code? (term e_1)) (not-code? (term e_2)))))
   (--> (in-hole E (b_0 (code e_1) (code e_2)))
        (in-hole E (reflect (b_0 e_1 e_2)))                               "bc")
   (--> (in-hole E (app (code e_1) (code e_2)))
        (in-hole E (reflect (app e_1 e_2)))                               "appc")
   (--> (in-hole E (lift (lit number_1)))
        (in-hole E (code (lit number_1)))                                 "lift-lit")
   (--> (in-hole E (lift (pair (code e_1) (code e_2))))
        (in-hole E (reflect (cons e_1 e_2)))                              "lift-pair")
   (--> (in-hole E (lift (code e))) (in-hole E (reflect (lift e)))        "lift-code")
   (--> (in-hole E (lift (lam x (code e))))
        (in-hole E (reflect (lam x e)))                                   "lift-lamc")
   (--> (in-hole E (lift (lam x e)))
        (in-hole E (lift (lam x (reify (subst x (code x) e)))))           "lift-lam"
        (side-condition (not-code? (term e))))
   (--> (in-hole E (run v e)) (in-hole E (run v (reify e)))               "run")
   (--> (in-hole E (run (code e_1) (code e_2)))
        (in-hole E (reflect (run e_1 e_2)))                               "runcc")
   (--> (in-hole E (run e_1 (code e_2)))
        (in-hole E (reify e_2))                                           "runc"
        (side-condition (not-code? (term e_1))))
   (--> (in-hole R (reify (in-hole E (reflect e))))
        (in-hole R (let x_new e (reify (in-hole E x_new))))               "reify-reflect"
        (where x_new ,(variable-not-in (term (R E e)) (term x))))
   (--> (in-hole R (reify e)) (in-hole R e)                               "reify-id")
   ))

(define-metafunction vm
  subst : x any any -> any
  [(subst x_1 any_1 (lam x_1 any_2)) (lam x_1 any_2)]
  [(subst x_1 any_1 (lam x_2 any_2))
   (lam x_new (subst x_1 any_1 (subst-var x_2 x_new any_2)))
   (where x_new ,(variable-not-in (term (x_1 any_1 any_2)) (term (x_2))))]
  [(subst x_1 any_1 x_1) any_1]
  [(subst x_1 any_1 x_2) x_2]
  [(subst x_1 any_1 (any_2 ...))
   ((subst x_1 any_1 any_2) ...)]
  [(subst x_1 any_1 any_2) any_2])

(define-metafunction vm
  subst-var : x any any -> any
  [(subst-var x_1 any_1 x_1) any_1]
  [(subst-var x_1 any_1 (any_2 ...))
   ((subst-var (x_1 any_1 any_2) ...))]
  [(subst-var x_1 any_1 any_2) any_2])

(define acc-trace
  (lambda (e)
    (define (helper e a)
      (let ((r (apply-reduction-relation red e)))
        (if (= 1 (length r))
            (helper (car r) (cons (car r) a))
            (reverse a))))
    (helper e (cons e '()))))

(define pp-each
  (lambda (l)
    (if (null? l) (display "done\n") (begin (display (car l)) (display "\n") (pp-each (cdr l))))))

(pp-each (acc-trace (term (reify (reflect (plus (lit 1) (lit 2)))))))
(pp-each (acc-trace (term (app (lam x x) (lit 2)))))
(pp-each (acc-trace (term (reify (lift (app (lam x x) (lit 2)))))))
(pp-each (acc-trace (term (lift (lam x x)))))
