(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-option :model-check-mode true)
(set-option :print-terms-cse false)

(set-logic QF_UF)
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun r () Bool)

; check non-binary xor rewrite
(push 1)
(assert (= p (not q) r))
(assert (xor p r))
(check-sat)
(get-proof)
(pop 1)

; check non-binary with two negated arguments
(push 1)
(assert (= p (not q) (not r)))
(assert (xor p (not r)))
(check-sat)
(get-proof)
(pop 1)

; check non-binary with no negated argument
(push 1)
(assert (= p q r))
(assert (xor p r))
(check-sat)
(get-proof)
(pop 1)

; check true rewrite
(push 1)
(assert (= p (not q) true r))
(assert (not p))
(check-sat)
(get-proof)
(pop 1)

; check false rewrite
(push 1)
(assert (= p (not q) false r))
(assert p)
(check-sat)
(get-proof)
(pop 1)
