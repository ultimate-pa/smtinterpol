(set-option :produce-interpolants true)
(set-info :source |
This files contains the interpolation queries for the examples in the paper

 M. Heizmann, J. Hoenicke, A. Podelski, Nested Interpolants, POPL 2010
|)
(set-info :status unsat)
(set-logic QF_UFLIA)
(declare-fun x_1 () Int)
(declare-fun xm1 () Int)
(declare-fun x2 () Int)
(declare-fun res4 () Int)
(declare-fun resm5 () Int)
(declare-fun xm6 () Int)
(declare-fun x7 () Int)
(declare-fun res9 () Int)
(declare-fun resm10 () Int)
(declare-fun res11 () Int)


;;
;;The interpolants of pi_3 in Figure 4
;;
;;Desired Interpolants:
;;   true
;;   true
;;   true
;;   x2 >= 101
;;   res4 = x2 - 10 && x2 >= 101
;;
;;Actual Interpolants:
;;Interpolant 0: true
;;Interpolant 1: true
;;Interpolant 2: true
;;Interpolant 3: (<= 0 (+ x2 (- 101)))
;;Interpolant 4: (and (<= res4 (+ x2 (- 10))) (<= 0 (+ res4 (- 91))))

(push 1)
(assert (! (<= x_1 100) :named phi_0))
(assert (! (and (<= xm1 (+ x_1 11)) (>= xm1 (+ x_1 11))) :named phi_1))
(assert (! (and (<= x2 xm1) (>= x2 xm1)) :named phi_2))
(assert (! (> x2 100) :named phi_3))
(assert (! (and (<= res4 (- x2 10)) (>= res4 (- x2 10))) :named phi_4))
(assert (! (and (<= x2 101) (distinct res4 91)) :named phi_5))
(check-sat)
(get-interpolants phi_0 phi_1 phi_2 phi_3 phi_4 phi_5)
(pop 1)

;;
;;This computes the interpolants for the nested trace pi_4 in Figure 6
;;
;;Desired Interpolants (see Figure 7):
;;   x_1 <= 100,
;;   xm1 <= 111,
;;
;;   true,
;;   res4 <= x2 - 10,
;;
;;   resm5 <= 101
;;   xm6 <= 101
;;
;;   x7 >= 101,
;;   x7 >= 101 && res <= x7 - 10
;;
;;   resm10 == 91
;;   res11  == 91
;;
;;Actual Interpolants:
;;
;;   (<= x_1 100)
;;   (<= xm1 111)
;;
;;   true
;;   (<= res4 (+ x2 (- 10)))
;;
;;   (<= resm5 101)
;;   (<= xm6 101)
;;
;;   (<= 0 (+ x7 (- 101)))
;;   (and (<= res9 (+ x7 (- 10))) (<= 0 (+ res9 (- 91))))
;;
;;   (and (<= resm10 91) (<= 0 (+ resm10 (- 91))))
;;   (let ((.cse0 (+ res11 (- 91))))
;;     (ite (not (<= (+ res11 (- 90)) 0))
;;          (=> (not (<= .cse0 0)) (<= res11 91))
;;          (<= 0 .cse0)))
;;
;;The last formula is equivalent to res11 == 91.

(push 1)
(assert (! (<= x_1 100) :named phi_0))
(assert (! (= xm1 (+ x_1 11)) :named phi_1))
(assert (! (= x2 xm1) :named phi_2))
(assert (! (> x2 100) :named phi_3))
(assert (! (= res4 (- x2 10)) :named phi_4))
(assert (! (= resm5 res4) :named phi_5))
(assert (! (= xm6 resm5) :named phi_6))
(assert (! (= x7 xm6) :named phi_7))
(assert (! (> x7 100) :named phi_8))
(assert (! (= res9 (- x7 10)) :named phi_9))
(assert (! (= resm10 res9) :named phi_10))
(assert (! (= res11 resm10) :named phi_11))
(assert (! (and (<= x_1 101) (distinct res11 91)) :named phi_12))
(check-sat)
(get-interpolants phi_0 phi_1 (phi_3 phi_4) (and phi_2 phi_5) phi_6
                  (phi_8 phi_9) (and phi_7 phi_10) phi_11 phi_12)
(pop 1)

(exit)
