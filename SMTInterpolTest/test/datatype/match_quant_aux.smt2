(set-info :smt-lib-version 2.6)
; a match below a quantifier gets a quantified aux literal (= @AUX true/false)
; in its matchCase tautologies, which the lowlevel conversion has to expand
(set-logic UFDTLIA)
(set-info :status unsat)

(declare-datatype L ((nil) (cons (hd Int) (tl L))))
(declare-fun k (Int) L)
(declare-fun P (Int) Bool)
(declare-fun f (Int) Int)

(assert (forall ((x Int)) (or (match (k x) ((nil (P x)) ((cons a b) (> a x)))) (= (f x) 11))))
(assert (= (k 0) nil))
(assert (not (P 0)))
(assert (not (= (f 0) 11)))

(check-sat)
(exit)
