(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-option :model-check-mode true)

(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () Bool)
(declare-fun b () Bool)

(assert (and (or a b false) (not a) (not b)))


(check-sat)
(set-option :print-terms-cse false)
(get-proof)