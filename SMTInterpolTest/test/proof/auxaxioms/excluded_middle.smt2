(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-option :model-check-mode true)

(set-logic QF_UF)
(declare-sort U 0)
(declare-fun x () Bool)
(declare-fun f (Bool) Bool)
(push 1)
(assert x)
(assert (not (= (f x) (f true))))
; (@tautology (! (or (= x true) (not x)) :excludedMiddle1)) 

(check-sat)
(set-option :print-terms-cse false)
(get-proof)

(pop 1)
(assert (not x))
(assert (not (= (f x) (f false))))
; (@tautology (! (or (= x false) x) :excludedMiddle2))

(check-sat)
(set-option :print-terms-cse false)
(get-proof)
