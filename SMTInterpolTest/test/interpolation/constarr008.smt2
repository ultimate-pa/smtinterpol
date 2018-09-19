(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-option :interpolant-check-mode true)
(set-option :print-terms-cse false)

(set-logic QF_AUFLIA)
(declare-sort U 0)
(declare-fun u1 () U)
(declare-fun u2 () U)
(declare-fun v () U)
(declare-fun w () U)
(declare-fun k1 () U)
(declare-fun k2 () U)
(declare-fun s () (Array U U))
(declare-fun p (U) Bool)

(assert (! (and (p v) (= ((as const (Array U U)) v) (store s k1 u1))) :named A))
(assert (! (and (not (p w)) (= ((as const (Array U U)) w) (store s k2 u2))) :named B))

(check-sat)
(get-proof)
(get-interpolants A B)
(exit)
