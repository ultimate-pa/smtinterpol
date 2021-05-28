(set-info :smt-lib-version 2.6)
(set-logic QF_DT)

(set-info :category "crafted")
(set-info :status unsat)

(declare-datatypes ( (List 0) (Nat 0) ) (
 ( (nil) (cons (car Nat) (cdr List) ))
 ( (zero) (succ (pred Nat)) )))

(declare-const a List)
(declare-const b List)

(assert (and (= a (cons zero b)) (not (= b nil)) (= (cdr b) a)))
(check-sat)
(exit)
