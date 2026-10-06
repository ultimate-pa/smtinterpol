(set-info :smt-lib-version 2.6)
; a Boolean match whose last case is a constructor case, not a default: the
; lowlevel conversion of its rewrite (convertMatch) used to treat the last
; case as another ite
(set-logic QF_UFDTLIA)
(set-info :status unsat)

(declare-datatype L ((nil) (cons (hd Int) (tl L))))
(declare-fun k (Int) L)
(declare-fun P (Int) Bool)
(declare-fun f (Int) Int)

(assert (or (match (k 0) ((nil (P 0)) ((cons a b) (> a 0)))) (= (f 0) 11)))
(assert (= (k 0) nil))
(assert (not (P 0)))
(assert (not (= (f 0) 11)))

(check-sat)
(exit)
