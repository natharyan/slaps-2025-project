(set-logic LIA)

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)

(define-fun Inv ((i Int) (sum Int)) Bool
  (<= (+ (* a i) (* b sum) c) 0)
)

; Initial state
(assert (Inv 0 0))

; Reachable states
(assert (Inv 1 0))
(assert (Inv 2 1))
(assert (Inv 3 3))
(assert (Inv 4 6))
(assert (Inv 5 10))
(assert (Inv 6 15))
(assert (Inv 10 45))
(assert (Inv 20 190))

; Transitions
(assert (=> (Inv 0 0) (Inv 1 0)))
(assert (=> (Inv 1 0) (Inv 2 1)))
(assert (=> (Inv 2 1) (Inv 3 3)))
(assert (=> (Inv 3 3) (Inv 4 6)))
(assert (=> (Inv 4 6) (Inv 5 10)))
(assert (=> (Inv 5 10) (Inv 6 15)))
(assert (=> (Inv 10 45) (Inv 11 55)))

; Adding states that violate weak invariants to try and get a stronger invariant (didn't get a very strong invariant, but better than previous values of 0, -1, 0)
(assert (not (Inv 100 1)))
(assert (not (Inv 50 1)))
(assert (not (Inv 30 5)))

; Both non-zero! 
(assert (not (= a 0)))
(assert (not (= b 0)))

; Excluding known weak solution
(assert (not (and (= a -1) (= b -1))))
(assert (not (and (= a 1) (= b 1))))

; Bounds
(assert (and (>= a -10) (<= a 10)))
(assert (and (>= b -10) (<= b 10)))
(assert (and (>= c -20) (<= c 20)))

(check-sat)
(get-model)