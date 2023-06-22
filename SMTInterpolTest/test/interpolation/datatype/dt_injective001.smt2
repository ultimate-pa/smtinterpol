(set-option :produce-interpolants true)
(set-option :interpolant-check-mode true)

(set-info :smt-lib-version 2.6)
(set-logic QF_DT)

(set-info :category "crafted")
(set-info :status unsat)


(declare-datatypes ( (List 0) (Nat 0) ) (
 ( (nil) (cons (car Nat) (cdr List) ))
 ( (zero) (succ (pred Nat)) )
))

(declare-const u List)
(declare-const v List)
(declare-const w List)

;; injective

(assert (! (not(= u v)) :named A ))
(assert (! (and (= (cons zero v) w) (= (cons zero u) w)) :named B )) 

(check-sat)
(get-interpolants A B)
(get-interpolants B A)
(exit)