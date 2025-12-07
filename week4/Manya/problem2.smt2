; problem2_non_linear.smt2
; Solve:
;   x^2 + y^2 = 25
;   x + y = 7
;   x > 0, y > 0, x,y in Z

(set-logic QF_NIA)  ; Quantifier-free Non-linear Integer Arithmetic

(declare-const x Int)
(declare-const y Int)

; constraints
(assert (= (+ (* x x) (* y y)) 25))
(assert (= (+ x y) 7))
(assert (> x 0))
(assert (> y 0))

(check-sat)
(get-model)
