(set-option :print-success false)
(set-option :produce-proofs true)
(set-option :interpolant-check-mode true)
(set-option :verbosity 3)
(set-logic QF_UF)
(set-info :source |Simple Craig interpolation example.|)
(set-info :interpolants ((and (= ab3 ab2) (= ab (g ab1)))))
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)
(declare-sort U 0)
(declare-fun a1 () U)
(declare-fun a2 () U)
(declare-fun b1 () U)
(declare-fun b2 () U)
(declare-fun ab () U)
(declare-fun ab1 () U)
(declare-fun ab2 () U)
(declare-fun ab3 () U)
(declare-fun fb (U) U)
(declare-fun g (U) U)
(assert (! (and (= a1 ab) (= a1 (g ab1)) (= ab2 a2) (= a2 ab3)) :named A))
(assert (!
 (and (= ab1 b2) (= b2 (fb ab2)) (= (fb ab3) (g ab1))
      (= ab1 b1) (not (= b1 ab))) :named B))
(check-sat)
(get-interpolants A B)
(exit)
