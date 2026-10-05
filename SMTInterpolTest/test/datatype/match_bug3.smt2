(set-info :smt-lib-version 2.6)
; a match consisting only of a default case: its matchDefault tautology has no
; ite chain, which used to crash the lowlevel proof conversion
(set-logic QF_UFDT)
(set-info :status unsat)

(declare-datatype Color ((red) (green) (blue)))
(declare-const c Color)
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)

(assert (or (match c ((x p))) q))
(assert (or (match c ((x p))) r))
(assert (not q))
(assert (not p))

(check-sat)
(exit)
