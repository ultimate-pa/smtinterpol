(set-info :smt-lib-version 2.6)
; a non-Boolean match below a quantifier: match terms are rewritten to their
; ite form, otherwise the quantified literal keeps the match and the
; quantifier theory fails (QuantClause.collectVarInfos)
(set-logic UFDTLIA)
(set-info :status unsat)

(declare-datatype L ((nil) (cons (hd Int) (tl L))))
(declare-fun k (Int) L)
(declare-fun g (Int) Int)

(assert (forall ((x Int)) (= (g x) (match (k x) ((nil 0) ((cons a b) (+ a x)))))))
(assert (= (k 2) (cons 1 nil)))
(assert (not (= (g 2) 3)))

(check-sat)
(exit)
