(set-logic QF_UFNIA)

(declare-const x Int)
(declare-const d Int)

(assert (not (= x (+ (* d (div x d)) (mod x d)))))
(assert (not (= d 0)))
(check-sat)
(get-proof)
