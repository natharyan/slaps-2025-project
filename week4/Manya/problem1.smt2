(set-logic UFLIA)

;; Explanation of synthesis- in the comments! 

;; Declare winning positions for 0 to 21
(declare-fun Winning (Int) Bool)

;; Base case: pile of 0 means current player loses (previous player took the last object)
(assert (= (Winning 0) false))

;; Explicitly defining each position from 1 to 21
;; A position is winning if there exists a move to a losing position

(assert (= (Winning 1) 
           (or (and (>= 1 1) (not (Winning (- 1 1)))))))

(assert (= (Winning 2) 
           (or (and (>= 2 1) (not (Winning (- 2 1))))
               (and (>= 2 2) (not (Winning (- 2 2)))))))

(assert (= (Winning 3) 
           (or (and (>= 3 1) (not (Winning (- 3 1))))
               (and (>= 3 2) (not (Winning (- 3 2))))
               (and (>= 3 3) (not (Winning (- 3 3)))))))

(assert (= (Winning 4) 
           (or (and (>= 4 1) (not (Winning (- 4 1))))
               (and (>= 4 2) (not (Winning (- 4 2))))
               (and (>= 4 3) (not (Winning (- 4 3)))))))

(assert (= (Winning 5) 
           (or (and (>= 5 1) (not (Winning (- 5 1))))
               (and (>= 5 2) (not (Winning (- 5 2))))
               (and (>= 5 3) (not (Winning (- 5 3)))))))

(assert (= (Winning 6) 
           (or (and (>= 6 1) (not (Winning (- 6 1))))
               (and (>= 6 2) (not (Winning (- 6 2))))
               (and (>= 6 3) (not (Winning (- 6 3)))))))

(assert (= (Winning 7) 
           (or (and (>= 7 1) (not (Winning (- 7 1))))
               (and (>= 7 2) (not (Winning (- 7 2))))
               (and (>= 7 3) (not (Winning (- 7 3)))))))

(assert (= (Winning 8) 
           (or (and (>= 8 1) (not (Winning (- 8 1))))
               (and (>= 8 2) (not (Winning (- 8 2))))
               (and (>= 8 3) (not (Winning (- 8 3)))))))

(assert (= (Winning 9) 
           (or (and (>= 9 1) (not (Winning (- 9 1))))
               (and (>= 9 2) (not (Winning (- 9 2))))
               (and (>= 9 3) (not (Winning (- 9 3)))))))

(assert (= (Winning 10) 
           (or (and (>= 10 1) (not (Winning (- 10 1))))
               (and (>= 10 2) (not (Winning (- 10 2))))
               (and (>= 10 3) (not (Winning (- 10 3)))))))

(assert (= (Winning 11) 
           (or (and (>= 11 1) (not (Winning (- 11 1))))
               (and (>= 11 2) (not (Winning (- 11 2))))
               (and (>= 11 3) (not (Winning (- 11 3)))))))

(assert (= (Winning 12) 
           (or (and (>= 12 1) (not (Winning (- 12 1))))
               (and (>= 12 2) (not (Winning (- 12 2))))
               (and (>= 12 3) (not (Winning (- 12 3)))))))

(assert (= (Winning 13) 
           (or (and (>= 13 1) (not (Winning (- 13 1))))
               (and (>= 13 2) (not (Winning (- 13 2))))
               (and (>= 13 3) (not (Winning (- 13 3)))))))

(assert (= (Winning 14) 
           (or (and (>= 14 1) (not (Winning (- 14 1))))
               (and (>= 14 2) (not (Winning (- 14 2))))
               (and (>= 14 3) (not (Winning (- 14 3)))))))

(assert (= (Winning 15) 
           (or (and (>= 15 1) (not (Winning (- 15 1))))
               (and (>= 15 2) (not (Winning (- 15 2))))
               (and (>= 15 3) (not (Winning (- 15 3)))))))

(assert (= (Winning 16) 
           (or (and (>= 16 1) (not (Winning (- 16 1))))
               (and (>= 16 2) (not (Winning (- 16 2))))
               (and (>= 16 3) (not (Winning (- 16 3)))))))

(assert (= (Winning 17) 
           (or (and (>= 17 1) (not (Winning (- 17 1))))
               (and (>= 17 2) (not (Winning (- 17 2))))
               (and (>= 17 3) (not (Winning (- 17 3)))))))

(assert (= (Winning 18) 
           (or (and (>= 18 1) (not (Winning (- 18 1))))
               (and (>= 18 2) (not (Winning (- 18 2))))
               (and (>= 18 3) (not (Winning (- 18 3)))))))

(assert (= (Winning 19) 
           (or (and (>= 19 1) (not (Winning (- 19 1))))
               (and (>= 19 2) (not (Winning (- 19 2))))
               (and (>= 19 3) (not (Winning (- 19 3)))))))

(assert (= (Winning 20) 
           (or (and (>= 20 1) (not (Winning (- 20 1))))
               (and (>= 20 2) (not (Winning (- 20 2))))
               (and (>= 20 3) (not (Winning (- 20 3)))))))

(assert (= (Winning 21) 
           (or (and (>= 21 1) (not (Winning (- 21 1))))
               (and (>= 21 2) (not (Winning (- 21 2))))
               (and (>= 21 3) (not (Winning (- 21 3)))))))

;; Query: Can player 1 win from position 21?
(check-sat)
(get-value ((Winning 21)))