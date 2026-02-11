;; Tree-Interpolation LIA
;; This computes the tree-interpolant for:
;;
;;          IP_2
;;         /    \
;;       IP_0   IP_1

(set-option :print-success false)
(set-option :produce-interpolants true)
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (! (> x y) :named IP_0))
(assert (! (= x 0) :named IP_1))
(assert (! (> y 0) :named IP_2))
(check-sat)
(get-interpolants IP_0 (IP_1) IP_2)
(exit)
