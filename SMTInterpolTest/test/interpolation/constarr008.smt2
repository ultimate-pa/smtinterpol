(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-option :interpolant-check-mode true)
(set-option :print-terms-cse false)

(set-logic QF_AUFLIA)
(declare-fun u1 () Int)
(declare-fun u2 () Int)
(declare-fun v () Int)
(declare-fun w () Int)
(declare-fun k1 () Int)
(declare-fun k2 () Int)
(declare-fun s () (Array Int Int))
(declare-fun p (Int) Bool)

(assert (! (and (p v) (= ((as const (Array Int Int)) v) (store s k1 u1))) :named A))
(assert (! (and (not (p w)) (= ((as const (Array Int Int)) w) (store s k2 u2))) :named B))

(check-sat)
(get-proof)
(get-interpolants A B)
(exit)
