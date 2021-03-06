(set-option :produce-proofs true)
(set-option :interpolant-check-mode true)

(set-logic QF_AX)
(declare-sort U 0)
(declare-fun i () U)
(declare-fun j () U)
(declare-fun k1 () U)
(declare-fun k2 () U)
(declare-fun k3 () U)
(declare-fun v1 () U)
(declare-fun v2 () U)
(declare-fun v3 () U)
(declare-fun a () (Array U U))
(declare-fun b () (Array U U))
(declare-fun s1 () (Array U U))
(declare-fun s2 () (Array U U))

(assert (! (and (not (= v2 v3)) (and (not (= v1 v2)) (and	(not (= v1 v3))
(and (not (= k1 i)) (and (not (= k2 i)) (and (not (= k3 i))
(= s1 (store (store s2 k1 v1) k2 v2)))))))) :named A))
(assert (! (and	(not (= (select a i) (select b j))) (and (= i j)
(and (= b (store s2 k3 v3)) (= a s1)))) :named B))

(check-sat)
(set-option :print-terms-cse false)
(get-proof)
(get-interpolants A B)
(exit)