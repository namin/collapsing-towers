#lang racket
(require redex)

(define-language vm
  (e x (lit number) (str string) (lam x e) (cons e e) (code e) (let x e e) (app e e) (if e e e) (a e) (b e e) (fix e) (lift e) (run e e)
     (reflect e) (lamc x e) (letc x e e))
  (v (lit number) (str string) (lam x e) (cons v v) (code e))
  (a car cdr isLit isStr isCons)
  (b plus minus times eq)
  (E hole (cons E e) (cons v E) (let x E e) (app E e) (app v E) (if E e e) (a E) (b E e) (b v E) (fix E) (lift E) (run E e) (reflect E))
  (M hole
     (cons M e) (cons v M) (let x M e) (app M e) (app v M) (if M e e) (a M) (b M e) (b v M) (fix M) (lift M) (run M e) (reflect M)
     (lift (lamc x M)) (if (code e) M e) (if (code e) v M) (run (code e) M) (letc x e M))
  (R (cons R e) (cons v R) (let x R e) (app R e) (app v R) (if R e e) (a R) (b R e) (b v R) (fix R) (lift R) (run R e) (reflect R)
     (lift (lamc x P)) (if (code e) P e) (if (code e) v P) (run (code e) P) (letc x e P))
  (P hole
     (cons R e) (cons v R) (let x R e) (app R e) (app v R) (if R e e) (a R) (b R e) (b v R) (fix R) (lift R) (run R e) (reflect R)
     (lift (lamc x P)) (if (code e) P e) (if (code e) v P) (run (code e) P) (letc x e P))
  (x (variable-except lit str lam cons let app if car cdr isLit isStr isCons plus minus times eq fix lift run reflect letc code)))

(define not-code? (lambda (x) (not ((redex-match vm (code e)) x))))
(define no-reflect? (lambda (x) (not ((redex-match vm (in-hole E (reflect any))) x))))

(define red
  (reduction-relation
   vm
   (--> (in-hole M (let x v e))                 (in-hole M (subst x v e)) "let")
   (--> (in-hole M (app (lam x e) v))           (in-hole M (subst x v e)) "lam")
   (--> (in-hole M (if (lit 0) e_1 e_2))        (in-hole M e_2)           "if0")
   (--> (in-hole M (if (lit number_0) e_1 e_2)) (in-hole M e_1)           "ifn"
        (side-condition (not (= 0 (term number_0)))))
   (--> (in-hole M (car (cons v_1 v_2))) (in-hole M v_1)                  "car")
   (--> (in-hole M (cdr (cons v_1 v_2))) (in-hole M v_2)                  "cdr")
   (--> (in-hole M (isLit (lit number))) (in-hole M (lit 1))              "isLit1")
   (--> (in-hole M (isLit v)) (in-hole M (lit 0))                         "isLit0"
        (side-condition (and (not-code? (term v)) (not ((redex-match vm (lit number)) (term v))))))
   (--> (in-hole M (isStr (str string))) (in-hole M (lit 1))              "isStr1")
   (--> (in-hole M (isStr v)) (in-hole M (lit 0))                         "isStr0"
        (side-condition (and (not-code? (term v)) (not ((redex-match vm (str string)) (term v))))))
   (--> (in-hole M (isCons (cons v_1 v_2))) (in-hole M (lit 1))           "isCons1")
   (--> (in-hole M (isCons v)) (in-hole M (lit 0))                         "isCons0"
        (side-condition (and (not-code? (term v)) (not ((redex-match vm (cons e_1 e_2)) (term v))))))
   (--> (in-hole M (plus (lit number_1) (lit number_2)))
        (in-hole M (lit ,(+ (term number_1) (term number_2))))             "plus")
   (--> (in-hole M (minus (lit number_1) (lit number_2)))
        (in-hole M (lit ,(- (term number_1) (term number_2))))             "minus")
   (--> (in-hole M (times (lit number_1) (lit number_2)))
        (in-hole M (lit ,(* (term number_1) (term number_2))))             "times")
   (--> (in-hole M (eq v_1 v_2))
        (in-hole M (lit ,(if (equal? (term v_1) (term v_2)) 1 0)))         "eq"
        (side-condition (and (not-code? (term v_1)) (not-code? (term v_2)))))
   (--> (in-hole M (fix (lam x e))) (in-hole M (subst x (fix (lam x e)) e)) "fix")
   (--> (in-hole M (if (code e_0) (code e_1) (code e_2)))
        (in-hole M (reflect (code (if e_0 e_1 e_2))))                     "ifccc")
   (--> (in-hole M (a_0 (code e_1)))
        (in-hole M (reflect (code (a_0 e_1))))                            "ac")
   (--> (in-hole M (b_0 (code e_1) (code e_2)))
        (in-hole M (reflect (code (b_0 e_1 e_2))))                        "bc")
   (--> (in-hole M (app (code e_1) (code e_2)))
        (in-hole M (reflect (code (app e_1 e_2))))                        "appc")
   (--> (in-hole M (fix (code e)))
        (in-hole M (reflect (code (fix e))))                              "fixc")
   (--> (in-hole M (lift (lit number_1)))
        (in-hole M (code (lit number_1)))                                 "lift-lit")
   (--> (in-hole M (lift (cons (code e_1) (code e_2))))
        (in-hole M (reflect (code (cons e_1 e_2))))                       "lift-cons")
   (--> (in-hole M (lift (code e))) (in-hole M (reflect (code (lift e)))) "lift-code")
   (--> (in-hole M (lift (lamc x (code e))))
        (in-hole M (reflect (code (lam x e))))                            "lift-lamc")
   (--> (in-hole M (lift (lam x e)))
        (in-hole M (lift (lamc x (subst x (code x) e))))                  "lift-lam")
   (--> (in-hole M (run (code e_1) (code e_2)))
        (in-hole M (reflect (code (run e_1 e_2))))                        "runcc")
   (--> (in-hole M (run v_1 (code e_2)))
        (in-hole M (app (lam x_new e_2) v_1))                             "runnc"
        (side-condition (not-code? (term v_1)))
        (where x_new ,(variable-not-in (term (M v_1 e_2)) (term x))))
   (--> (in-hole P (in-hole E (reflect (code e))))
        (in-hole P (letc x_new e (in-hole E (code x_new))))               "reify-reflect"
        (where x_new ,(variable-not-in (term (R E e)) (term x))))
   (--> (in-hole M (letc x_1 e_1 (code e_2)))
        (in-hole M (code (let x_1 e_1 e_2)))                              "letc")
   ))

(define-metafunction vm
  subst : x any any -> any
  [(subst x_1 any_1 (lam x_1 any_2)) (lam x_1 any_2)]
  [(subst x_1 any_1 (lam x_2 any_2))
   (lam x_new (subst x_1 any_1 (subst-var x_2 x_new any_2)))
   (where x_new ,(variable-not-in (term (x_1 any_1 any_2)) (term x_2)))]
  [(subst x_1 any_1 (let x_1 any_x any_2)) (let x_1 (subst x_1 any_1 any_x) any_2)]
  [(subst x_1 any_1 (let x_2 any_x any_2))
   (let x_new (subst x_1 any_1 any_x) (subst x_1 any_1 (subst-var x_2 x_new any_2)))
   (where x_new ,(variable-not-in (term (x_1 any_1 any_2)) (term x_2)))]
  [(subst x_1 any_1 (letc x_1 any_x any_2)) (letc x_1 (subst x_1 any_1 any_x) any_2)]
  [(subst x_1 any_1 (letc x_2 any_x any_2))
   (letc x_new (subst x_1 any_1 any_x) (subst x_1 any_1 (subst-var x_2 x_new any_2)))
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

(define pp-fl
  (lambda (l)
    (pp-each (list (car l) (last l)))))

(define fac
  `(fix (app l (lam fac (app l (lam n
   (if n
       (times n (app fac (minus n (app l (lit 1)))))
       (app l (lit 1)))))))))

;(pp-each (acc-trace (term (app (let l (lam x x) ,fac) (lit 3)))))
;(pp-each (acc-trace (second (last (acc-trace (term (app (let l (lam x (lift x)) ,fac) (lift (lit 3)))))))))

(define evl (lambda (l)
  `(fix (lam ev (lam exp (lam env
   (if (isLit exp) ,(l `exp)
   (if (isStr exp) (app env exp)
   (if (eq (str "plus")  (car exp)) (plus  (app (app ev (car (cdr exp))) env) (app (app ev (car (cdr (cdr exp)))) env))
   (if (eq (str "minus") (car exp)) (minus (app (app ev (car (cdr exp))) env) (app (app ev (car (cdr (cdr exp)))) env))
   (if (eq (str "times") (car exp)) (times (app (app ev (car (cdr exp))) env) (app (app ev (car (cdr (cdr exp)))) env))
   (if (eq (str "eq")    (car exp)) (eq    (app (app ev (car (cdr exp))) env) (app (app ev (car (cdr (cdr exp)))) env))
   (if (eq (str "if")    (car exp)) (if (app (app ev (car (cdr exp))) env) (app (app ev (car (cdr (cdr exp)))) env) (app (app ev (car (cdr (cdr (cdr exp))))) env))
   (if (eq (str "lam")   (car exp)) ,(l `(lam x (app (app ev (car (cdr (cdr exp)))) (lam y (if (eq y (car (cdr exp))) x (app env y))))))
   (if (eq (str "let")   (car exp)) (let x (app (app ev (car (cdr (cdr exp)))) env) (app (app ev (car (cdr (cdr (cdr exp))))) (lam y (if (eq y (car (cdr exp))) x (app env y)))))
   (if (eq (str "fix")   (car exp)) (fix (app (app ev (car (cdr exp))) env))
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

;(pp-each (acc-trace (term (app (app (let l (lam x x) ,ev) (lit 3)) (lam y y)))))
;(pp-each (acc-trace (term (app (app (let l (lam x (lift x)) ,ev) (lit 3)) (lam y y)))))

(define quotify
  (lambda (e)
    (if (or (not (pair? e)) (eq? (car e) 'lit) (eq? (car e) 'str) (eq? (car e) 'code))
        (if (symbol? e) (list 'str (symbol->string e)) (if (null? e) (list 'str "nil") e))
        (list 'cons (quotify (car e)) (quotify (cdr e))))))

(define facl (lambda (l)
  `(fix ,(l `(lam fac ,(l `(lam n
   (if n
       (times n (app fac (minus n ,(l `(lit 1)))))
       ,(l `(lit 1))))))))))

;(pp-fl (acc-trace (term (app (app (let l (lam x x) ,ev) ,(quotify '(times (plus (lit 1) (lit 2)) (lit 4)))) (lam y y)))))
;(pp-fl (acc-trace (term (app (app (let l (lam x (lift x)) ,ev) ,(quotify '(times (plus (lit 1) (lit 2)) (lit 4)))) (lam y y)))))
;(pp-fl (acc-trace (term (app (app (let l (lam x x) ,ev) ,(quotify '(app (lam x (times x x)) (lit 3)))) (lam y y)))))
;(pp-fl (acc-trace (term (app (app (let l (lam x (lift x)) ,ev) ,(quotify '(lam x (times x x)))) (lam y y)))))
;(pp-fl (acc-trace (term (app (app (let l (lam x x) ,ev) ,(quotify `(if (lit 1) (lit 1) (lit 0)))) (lam y y)))))
;(pp-fl (acc-trace (term (app (app (let l (lam x x) ,ev) ,(quotify `(app (lam x (if x (lit 1) (lit 0))) (lit 3)))) (lam y y)))))
;(length (acc-trace (term (app (app (let l (lam x x) ,ev) ,(quotify `(app ,(facl (lambda (x) x)) (lit 3)))) (lam y y)))))
;(length (acc-trace (term (app (app ,(evl (lambda (x) x)) ,(quotify `(app ,(facl (lambda (x) x)) (lit 3)))) (lam y y)))))
;(length (acc-trace (term (app (app (let l (lam x x) ,ev) ,(quotify `(app (let l (lam x x) ,(facl (lambda (x) x))) (lit 3)))) (lam y y)))))
;(length (acc-trace (term (app (app (let l (lam x x) ,ev) ,(quotify `(app (let l (lam x x) ,fac) (lit 3)))) (lam y y)))))
;(length (acc-trace (term (app (app ,(evl (lambda (x) x)) ,(quotify `(app (let l (lam x x) ,fac) (lit 3)))) (lam y y)))))
;(pp-fl (acc-trace (term (app (app (let l (lam x (lift x)) ,ev) ,(quotify (facl (lambda (x) x)))) (lam y y)))))
;(pp-fl (acc-trace `(app
;                    ,(second (last (acc-trace (term (app (app ,(evl (lambda (x) `(lift ,x))) ,(quotify (facl (lambda (x) x)))) (lam y y))))))
;                    (lit 3))))
;(pp-fl (acc-trace `(app (app
;,(second (last (acc-trace `(app (app ,(evl (lambda (x) `(lift ,x))) ,(quotify (evl (lambda (x) x)))) (lam y y)))))
;,(quotify '(app (lam x (plus x x)) (lit 3)))) (lam y y))))
;(last (acc-trace (term (app (app ,(evl (lambda (x) x)) ,(quotify `(app (app ,(evl (lambda (x) x)) (lit 3)) (lam y y)))) (lam y y)))))
;(last (acc-trace (term (app (app ,(evl (lambda (x) x)) ,(quotify `(app (app ,(evl (lambda (x) `(lift ,x))) (lit 3)) (lam y y)))) (lam y y)))))
;(last (acc-trace (term (app (app ,(evl (lambda (x) x)) ,(quotify `(app (app ,(evl (lambda (x) x)) (app (lam x x) (lit 3))) (lam y y)))) (lam y y)))))
;(last (acc-trace (term (app (app ,(evl (lambda (x) x)) ,(quotify `(app (app ,(evl (lambda (x) `(lift ,x))) (app (lam x x) (lit 3))) (lam y y)))) (lam y y)))))
;(last (acc-trace (term (app (app ,(evl (lambda (x) x)) ,(quotify `(app (app ,(evl (lambda (x) `(lift ,x))) (lam x x)) (lam y y)))) (lam y y)))))

;; BUG
;(define ds (acc-trace (term (app (app ,(evl (lambda (x) `(lift ,x))) ,(quotify '(lam exp (eq (str "foo") (car exp))))) (lam y y)))))