(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-option :model-check-mode true)

(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () Bool)
(declare-fun b () Bool)

(assert (and (not (or a (and a b))) a))


(check-sat)
(set-option :print-terms-cse false)
(get-proof)