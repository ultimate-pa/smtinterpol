(set-info :smt-lib-version 2.6)
; a non-Boolean match below a quantifier, as argument of an uninterpreted
; function: match terms are rewritten to their ite form, otherwise the
; quantified literal keeps the match and the quantifier theory fails
; (QuantClause.addVarArgInfo)
(set-logic UFDTLIA)
(set-info :status unsat)

(declare-datatype L ((nil) (cons (hd Int) (tl L))))
(declare-fun k (Int) L)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)

(assert (forall ((x Int)) (= (f (match (k x) ((nil 0) ((cons a b) (+ a x))))) (g x))))
(assert (= (k 2) (cons 1 nil)))
(assert (not (= (f 3) (g 2))))

(check-sat)
(exit)
