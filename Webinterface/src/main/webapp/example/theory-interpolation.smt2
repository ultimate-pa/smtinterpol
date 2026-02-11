;; Interpolation in UFLIA
;;
(set-option :produce-proofs true)
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (! (and (< (f x) (g y)) (= x y)) :named CCPart))
(assert (! (and (> (f z) (g x)) (= z x)) :named LAPart))
(check-sat)
(get-interpolants CCPart LAPart)
(exit)

