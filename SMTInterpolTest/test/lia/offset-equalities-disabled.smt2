; Offset equalities can be switched off with the :offset-equalities option, which
; falls back to plain congruence closure: every offset is zero and a numeric term
; keeps its constant instead of carrying it as an offset.  The same problems must
; still be solved and proven.  This is the same conflict as
; offset-equality-parity-conflict, plus a congruence over an offsetted argument,
; which without offsets needs the shared term equality (+ y 1) = x instead.
(set-option :offset-equalities false)
(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-logic QF_UFLIA)
(set-info :status unsat)
(declare-fun f (Int) Int)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (= x (+ y 1)))
(assert (not (= (f (+ y 1)) (f x))))
(check-sat)
(push 1)
(assert (= (* 2 x) z))
(assert (= (* 2 y) (+ z 1)))
(check-sat)
(pop 1)
(exit)
