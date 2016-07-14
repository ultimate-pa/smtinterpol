(set-option :produce-proofs true)
(set-option :proof-check-mode false)
(set-option :model-check-mode false)

(set-logic QF_UF)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)

(assert (or c (not (or a b (not a)))))
(assert (not c))

(check-sat)
(set-option :print-terms-cse false)
(get-proof)