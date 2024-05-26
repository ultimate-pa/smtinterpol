(set-logic QF_UFNIA)

(declare-const x Int)
(declare-const d Int)

(assert (not (= x (+ (* d (div x d)) (mod x d)))))
(check-sat)
(get-model)

(assert (not (= d 0)))
(check-sat)
(get-proof)
