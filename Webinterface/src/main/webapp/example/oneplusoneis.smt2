; What is 1 + 1?

(set-option :produce-proofs true)
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (= (+ 1 1) x))
(check-sat)
(get-proof)
