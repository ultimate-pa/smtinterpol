(set-logic QF_LIA)
(declare-const x Int)

(assert (= (div x 0) 5))
(assert (= (div (div x 0) 0) 5))
(assert (not (= (div 5 0) 5)))
(check-sat)
