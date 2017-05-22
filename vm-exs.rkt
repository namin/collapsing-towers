#lang racket
(require "vm.rkt")

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