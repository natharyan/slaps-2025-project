(set-logic AUFLIA)

; most invariants were failing universal induction, even though they are valid loop invariants- restricting induction to reachable states but finitely (otherwise it was not terminating)

; hardcoded invariant answers from problem3.smt2 
(define-fun a () Int 1)
(define-fun b () Int -1)
(define-fun c () Int -1)

(define-fun Inv ((i Int) (sum Int)) Bool
  (<= (+ (* a i) (* b sum) c) 0)
)

(assert (Inv 0 0))
(assert (Inv 1 0))
(assert (Inv 2 1))
(assert (Inv 3 3))
(assert (Inv 4 6))
(assert (Inv 5 10))
(assert (Inv 6 15))
(assert (Inv 10 45))

(assert (=> (Inv 0 0) (Inv 1 0)))
(assert (=> (Inv 1 0) (Inv 2 1)))
(assert (=> (Inv 2 1) (Inv 3 3)))
(assert (=> (Inv 3 3) (Inv 4 6)))
(assert (=> (Inv 4 6) (Inv 5 10)))
(assert (=> (Inv 5 10) (Inv 6 15)))
(assert (=> (Inv 10 45) (Inv 11 55)))

(check-sat)