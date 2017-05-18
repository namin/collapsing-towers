#lang racket
(require redex)

(define-language vm
  (e x (lit number) (lam x e) (cons e e) (code e) (let x e e) (app e e) (if e e e) (b e e) (fix e) (lift e) (run e e)
     (reflect e) (reify e))
  (v (lit number) (lam x e) (cons v v) (code e))
  (b plus minus times)
  (E hole (cons E e) (cons v E) (let x E e) (app E e) (app v E) (if E e e) (b E e) (b v E) (fix E e) (lift E) (run E e) (reflect E))
  (R hole (reify R) (lift (lam x R)) (if (code e) R e) (if (code e) v R) (run (code e) R))
  (M (in-hole R (reify E)) E)
  (x (variable-except lit lam cons let app if plus minus times fix lift run reflect reify pair code)))

(define not-code? (lambda (x) (not ((redex-match vm (code e)) x))))
(define no-reflect? (lambda (x) (not ((redex-match vm (in-hole E (reflect any))) x))))
(define no-reify? (lambda (x) (not ((redex-match vm (in-hole R (reify any))) x))))

(define red
  (reduction-relation
   vm
   (--> (in-hole M (let x v e))                 (in-hole M (subst x v e)) "let")
   (--> (in-hole M (app (lam x e) v))           (in-hole M (subst x v e)) "lam")
   (--> (in-hole M (if (lit 0) e_1 e_2))        (in-hole M e_2)           "if0")
   (--> (in-hole M (if (lit number_1) e_1 e_2)) (in-hole M e_1)           "ifn"
        (side-condition (not (= 0 (term number_1)))))
   (--> (in-hole M (plus (lit number_1) (lit number_2)))
        (in-hole M (lit ,(+ (term number_1) (term number_2))))             "plus")
   (--> (in-hole M (minus (lit number_1) (lit number_2)))
        (in-hole M (lit ,(- (term number_1) (term number_2))))             "minus")
   (--> (in-hole M (times (lit number_1) (lit number_2)))
        (in-hole M (lit ,(* (term number_1) (term number_2))))             "times")
   (--> (in-hole M (fix (lam x e))) (in-hole M (subst x (fix (lam x e)) e)) "fix")
   (--> (in-hole M (cons v_1 v_2))  (in-hole M (pair v_1 v_2))            "cons")
   (--> (in-hole M (if (code e_0) (code e_1) (code e_2)))
        (in-hole M (reflect (code (if (code e_0) e_1 e_2))))              "ifccc")
   (--> (in-hole M (if (code e_0) e_1 e_2))
        (in-hole M (if (code e_0) (reify e_1) (reify e_2)))               "ifc"
        (side-condition (and (not-code? (term e_1)) (not-code? (term e_2)))))
   (--> (in-hole M (b_0 (code e_1) (code e_2)))
        (in-hole M (reflect (code (b_0 e_1 e_2))))                        "bc")
   (--> (in-hole M (app (code e_1) (code e_2)))
        (in-hole M (reflect (code (app e_1 e_2))))                        "appc")
   (--> (in-hole M (lift (lit number_1)))
        (in-hole M (code (lit number_1)))                                 "lift-lit")
   (--> (in-hole M (lift (cons (code e_1) (code e_2))))
        (in-hole M (reflect (code (cons e_1 e_2))))                       "lift-pair")
   (--> (in-hole M (lift (code e))) (in-hole M (reflect (lift e)))        "lift-code")
   (--> (in-hole M (lift (lam x (code e))))
        (in-hole M (reflect (code (lam x e))))                            "lift-lamc")
   (--> (in-hole M (lift (lam x e)))
        (in-hole M (lift (lam x (reify (subst x (code x) e)))))           "lift-lam"
        (side-condition (and (not-code? (term e)) (no-reify? (term e)))))
   (--> (in-hole M (run v e)) (in-hole M (run v (reify e)))               "run")
   (--> (in-hole M (run (code e_1) (code e_2)))
        (in-hole M (reflect (code (run e_1 e_2))))                        "runcc")
   (--> (in-hole M (run e_1 (code e_2)))
        (in-hole M (reify e_2))                                           "runc"
        (side-condition (not-code? (term e_1))))
   (--> (in-hole R (reify (in-hole E (reflect (code e)))))
        (in-hole R (let x_new (code e) (reify (in-hole E x_new))))        "reify-reflect"
        (where x_new ,(variable-not-in (term (R E e)) (term x))))
   (--> (in-hole R (reify v)) (in-hole R v)                               "reify-id"
        (side-condition (no-reflect? (term v))))
   ))

(define-metafunction vm
  subst : x any any -> any
  [(subst x_1 any_1 (lam x_1 any_2)) (lam x_1 any_2)]
  [(subst x_1 any_1 (lam x_2 any_2))
   (lam x_new (subst x_1 any_1 (subst-var x_2 x_new any_2)))
   (where x_new ,(variable-not-in (term (x_1 any_1 any_2)) (term x_2)))]
  [(subst x_1 any_1 x_1) any_1]
  [(subst x_1 any_1 x_2) x_2]
  [(subst x_1 any_1 (any_2 ...))
   ((subst x_1 any_1 any_2) ...)]
  [(subst x_1 any_1 any_2) any_2])

(define-metafunction vm
  subst-var : x any any -> any
  [(subst-var x_1 any_1 x_1) any_1]
  [(subst-var x_1 any_1 (any_2 ...))
   ((subst-var x_1 any_1 any_2) ...)]
  [(subst-var x_1 any_1 any_2) any_2])

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

(pp-each (acc-trace (term (reify (reflect (code (plus (lit 1) (lit 2))))))))
(pp-each (acc-trace (term (reify (lift (plus (lit 1) (lit 2)))))))
(pp-each (acc-trace (term (reify (app (lam x x) (lit 2))))))
(pp-each (acc-trace (term (reify (lift (app (lam x x) (lit 2)))))))
(pp-each (acc-trace (term (reify (lift (lam x x))))))
(pp-each (acc-trace (term (reify (lift (if (lit 0) (lit 1) (plus (lit 1) (lit 2))))))))
(pp-each (acc-trace (term (reify (if (lit 0) (lift (plus (lit 3) (lit 1))) (plus (lift (lit 1)) (lift (lit 2))))))))
(pp-each (acc-trace (term (reify (plus (lift (lit 0)) (plus (lift (lit 1)) (lift (plus (lit 2) (lit 3)))))))))
(pp-each (acc-trace (term (reify (plus (plus (lift (lit 0)) (lift (lit 1))) (plus (lift (lit 2)) (lift (lit 3))))))))


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

(pp-each (acc-trace (term (reify (lift (lam x (lift (plus (lit 1) (lit 2)))))))))

(pp-each (acc-trace (term (reify (lift (lam x (plus x (lift (plus (lit 1) (lit 2))))))))))