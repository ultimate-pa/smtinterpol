(set-option :produce-models true)
(set-logic QF_UFLIRA)
(declare-fun f (Int) Real)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (= (to_real a) (f a)))
(assert (= (f b) (/ 1.0 2.0)))
(assert (= a b))
(check-sat)
;(get-model)
(exit)
