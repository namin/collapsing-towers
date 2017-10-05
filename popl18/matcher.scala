// Regular expression matchers as user-level mini-interpreters

import Base._
import Lisp._

object Matcher {
  val matcher_poly_src = """
  (let star_loop (lambda star_loop m (lambda _ c (maybe-lift (lambda inner_loop s
  (if (eq?  (maybe-lift 'yes) (m s)) (maybe-lift 'yes)
  (if (eq?  (maybe-lift 'done) (car s)) (maybe-lift 'no)
  (if (eq?  '_ c) (inner_loop (cdr s))
  (if (eq?  (maybe-lift c) (car s)) (inner_loop (cdr s)) (maybe-lift 'no)))))))))
(let match_here (lambda match_here r (lambda _ s (if (eq?  'done (car r)) (maybe-lift 'yes)
  (let m (lambda _ s
      (if (eq?  '_ (car r)) (if (eq?  (maybe-lift 'done) (car s)) (maybe-lift 'no) ((match_here (cdr r)) (cdr s)))
      (if (eq?  (maybe-lift 'done) (car s)) (maybe-lift 'no)
      (if (eq?  (maybe-lift (car r)) (car s)) ((match_here (cdr r)) (cdr s)) (maybe-lift 'no)))))
    (if (eq?  'done (car (cdr r))) (m s)
    (if (eq?  '* (car (cdr r))) (((star_loop (match_here (cdr (cdr r)))) (car r)) s) (m s)))))))
(let match (lambda match r
  (if (eq?  'done (car r)) (maybe-lift (lambda _ s (maybe-lift 'yes))) (maybe-lift (match_here r))))
match)))"""

  val matcher_src = s"(let maybe-lift (lambda _  e e) $matcher_poly_src)"
  val matcherc_src = s"(let maybe-lift (lambda _  e (lift e)) $matcher_poly_src)"

  def test() = {
    println("// ------- Matcher.test --------")

    checkrun(s"(($matcher_src '(_ * a _ * done)) '(b a done))", "Str(yes)")
    checkrun(s"(($matcher_src '(_ * a _ * done)) '(b b done))", "Str(no)")
    checkrun(s"((run 0 ($matcherc_src '(_ * a _ * done))) '(b a done))", "Str(yes)")
    checkrun(s"((run 0 ($matcherc_src '(_ * a _ * done))) '(b b done))", "Str(no)")

    checkcode(s"($matcherc_src '(a b done))",
    """(lambda f0 x1 
  (let x2 (car x1) 
  (let x3 (eq? 'done x2) 
  (if x3 'no 
  
    (let x4 (car x1) 
    (let x5 (eq? 'a x4) 
    (if x5 
      (let x6 (cdr x1) 
      (let x7 (car x6) 
      (let x8 (eq? 'done x7) 
      (if x8 'no 
      
        (let x9 (car x6) 
        (let x10 (eq? 'b x9) 
        (if x10 
          (let x11 (cdr x6) 'yes) 
        'no))))))) 
    'no)))))))""")

    // deriving translators
    import PinkBase._
    val instr_poly_src = Pink.ev_poly_src.replace("(env exp)", "(if (eq? 's exp) (log (maybe-lift2 0) (env exp)) (env exp))")
    val instr_src = ev_nil(ev_nolift(s"(let maybe-lift2 (lambda _ x x) $instr_poly_src)"))
    val instr2_src = ev_nil(ev_nolift(s"(let maybe-lift2 (lambda _ x (lift x)) $instr_poly_src)"))
    val instrc_src = ev_nil(ev_lift(s"(let maybe-lift2 (lambda _ x (lift (lift x))) $instr_poly_src)"))
    val log_ab_code = """(lambda f0 x1 
  (let x2 (log 0 x1) 
  (let x3 (log 0 x2) 
  (let x4 (car x3) 
  (let x5 (eq? 'done x4) 
  (if x5 'no 
  
    (let x6 (log 0 x2) 
    (let x7 (car x6) 
    (let x8 (eq? 'a x7) 
    (if x8 
      (let x9 (log 0 x2) 
      (let x10 (cdr x9) 
      (let x11 (log 0 x10) 
      (let x12 (log 0 x11) 
      (let x13 (car x12) 
      (let x14 (eq? 'done x13) 
      (if x14 'no 
      
        (let x15 (log 0 x11) 
        (let x16 (car x15) 
        (let x17 (eq? 'b x16) 
        (if x17 
          (let x18 (log 0 x11) 
          (let x19 (cdr x18) 'yes)) 
        'no))))))))))) 
    'no))))))))))"""
    val logres = "Tup(Str(a),Tup(Str(b),Tup(Str(done),Str(.))));Tup(Str(a),Tup(Str(b),Tup(Str(done),Str(.))));Tup(Str(a),Tup(Str(b),Tup(Str(done),Str(.))));Tup(Str(a),Tup(Str(b),Tup(Str(done),Str(.))));Tup(Str(b),Tup(Str(done),Str(.)));Tup(Str(b),Tup(Str(done),Str(.)));Tup(Str(b),Tup(Str(done),Str(.)));Tup(Str(b),Tup(Str(done),Str(.)));"
    checkrunlog(s"((($instr_src '$matcher_src) '(a b done)) '(a b done))", "Str(yes)", logres)
    checkrunlog(s"((run 0 (($instr2_src '$matcherc_src) '(a b done))) '(a b done))", "Str(yes)", logres)
    checkrunlog(s"((run 0 ((run 0 ($instrc_src '$matcherc_src)) '(a b done))) '(a b done))", "Str(yes)", logres)
    checkcode(s"(($instr2_src '$matcherc_src) '(a b done))", log_ab_code)
    checkcode(s"((run 0 ($instrc_src '$matcherc_src)) '(a b done))", log_ab_code)

    testDone()
  }
}
