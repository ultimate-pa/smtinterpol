(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-option :model-check-mode true)
(set-option :print-terms-cse false)

(set-logic QF_UF)
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun r () Bool)

; check distinct with more than two parameters
(push 1)
(assert (distinct p q r))
(check-sat)
(get-proof)
(pop 1)

; check binary distinct 
(push 1)
(assert (distinct p q))
(assert p)
(assert q)
(check-sat)
(get-proof)
(pop 1)

; check binary distinct with negated arguments
(push 1)
(assert (distinct p (not q)))
(assert (distinct (not q) r))
(assert p)
(assert (not r))
(check-sat)
(get-proof)
(pop 1)

; check non-binary with two negated argument
(push 1)
(assert (distinct (not p) (not q)))
(assert p)
(assert q)
(check-sat)
(get-proof)
(pop 1)

; check true and false rewrites
(push 1)
(assert (distinct p true))
(assert (distinct p false))
(check-sat)
(get-proof)
(pop 1)

(push 1)
(assert (distinct true p))
(assert (distinct false p))
(check-sat)
(get-proof)
(pop 1)

; check distinct same
(push 1)
(assert (distinct p p))
(check-sat)
(get-proof)
(pop 1)

; check distinct opposite
(push 1)
(assert (not (distinct p (not p))))
(check-sat)
(get-proof)
(pop 1)
