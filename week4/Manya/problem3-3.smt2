; stronger check than necessary (non linear support is not there in AUFLIA) 
; tried to implement set-logic HORN but couldn't 


(set-logic AUFLIA)

; hardcoded invariant answers from problem3.smt2 
(define-fun a () Int 1)
(define-fun b () Int -1)
(define-fun c () Int -1)

(define-fun Inv ((i Int) (sum Int)) Bool
  (<= (+ (* a i) (* b sum) c) 0)
)

; Base case
(assert (Inv 0 0))

; Universal inductive step
(assert 
  (forall ((i Int) (sum Int))
    (=> (and (>= i 0) (>= sum 0) (Inv i sum))
        (Inv (+ i 1) (+ sum i)))
  )
)

(check-sat)