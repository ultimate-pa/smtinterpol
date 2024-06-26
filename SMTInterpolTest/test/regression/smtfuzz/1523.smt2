(set-option :produce-unsat-cores true)
(set-info :expect-errors 225)
(set-logic NRA)
(declare-fun v0 () Bool)
(declare-fun v1 () Bool)
(declare-fun v2 () Bool)
(declare-fun v3 () Bool)
(declare-fun v4 () Bool)
(declare-fun r0 () Real)
(declare-fun r2 () Real)
(declare-fun r4 () Real)
(declare-fun r5 () Real)
(declare-fun r7 () Real)
(assert (forall ((q0 Real) (q1 Real) (q2 Real)) (not (= r7 r4))))
(assert (exists ((q3 Real) (q4 Real) (q5 Real)) (not (distinct q4 q5 (/ 90719737.0 r5)))))
(assert (exists ((q3 Real) (q5 Real) ) (forall ((q4 Real) ) (not (< q3 r7 r4 80121.0 r7)))))
(assert (! (not v3) :named IP_1))
(declare-fun r8 () Real)
(declare-fun v5 () Bool)
(assert (not (exists ((q6 Bool) (q7 Real)) v5)))
(push 1)
(assert (not (exists ((q8 Bool)) (not (or v1 q8 q8 q8)))))
(declare-fun v6 () Bool)
(assert (! (=> v1 v2) :named IP_2))
(assert (! (=> (=> v1 v2) v4) :named IP_3))
(check-sat-assuming (IP_1 IP_2))
(get-unsat-core)
(pop 1)
(push 1)
(declare-fun v7 () Bool)
(assert (exists ((q9 Real) (q10 Real) (q11 Bool)) (=> (distinct q11 v1 v7 v5 q11 v5) (distinct q9 q10 80121.0 90719737.0))))
(assert (! v0 :named IP_4))
(check-sat-assuming (IP_1 IP_3))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_3))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_2))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_2))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_3))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_3))
(get-unsat-core)
(assert (! (not v0) :named IP_5))
(check-sat-assuming (IP_1 IP_3))
(get-unsat-core)
(check-sat-assuming (IP_3 IP_4))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_3))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_2))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_4))
(get-unsat-core)
(declare-fun v8 () Bool)
(assert (not (forall ((q12 Bool)) (not (= q12 q12 (not v0) (not v0) q12)))))
(check-sat-assuming (IP_1 IP_3))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_4))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_4))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_2))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_3))
(get-unsat-core)
(declare-fun v9 () Bool)
(assert (exists ((q13 Real) (q14 Bool)) (=> (> q13 (/ 90719737.0 r5) q13 r0) (= v4 (<= r7 90719737.0 r4 80121.0 r8) q14 v2 v8 q14))))
(check-sat-assuming (IP_1 IP_4))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_2))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_4))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_3))
(get-unsat-core)
(check-sat-assuming (IP_3 IP_4))
(get-unsat-core)
(push 1)
(assert (exists ((q15 Bool) (q16 Bool) (q17 Bool)) (not (= q17 q17 q15 v1 q17 v2 q15 q16))))
(assert (! v1 :named IP_6))
(check-sat-assuming (IP_2 IP_4))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_2))
(get-unsat-core)
(check-sat-assuming (IP_3 IP_5))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_3))
(get-unsat-core)
(check-sat-assuming (IP_3 IP_4))
(get-unsat-core)
(check-sat)
(check-sat-assuming (IP_2 IP_4))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_5))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_3))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_5))
(get-unsat-core)
(check-sat-assuming (IP_4 IP_5))
(get-unsat-core)
(assert (exists ((q18 Real)) v8))
(assert (! (not v5) :named IP_7))
(check-sat-assuming (IP_1 IP_6))
(get-unsat-core)
(check-sat-assuming (IP_4 IP_6))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_4))
(get-unsat-core)
(check-sat-assuming (IP_3 IP_6))
(get-unsat-core)
(check-sat-assuming (IP_4 IP_5))
(get-unsat-core)
(pop 1)
(assert (not (forall ((q19 Bool) (q20 Bool) (q21 Bool) (q22 Real)) v4)))
(check-sat-assuming (IP_2 IP_4))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_2))
(get-unsat-core)
(check-sat-assuming (IP_3 IP_6))
(get-unsat-core)
(check-sat-assuming (IP_3 IP_4))
(get-unsat-core)
(check-sat-assuming (IP_3 IP_5))
(get-unsat-core)
(declare-fun v10 () Bool)
(assert (exists ((q23 Bool)) (not (or (distinct (not v3) v3 v4 (not v3) (<= r7 90719737.0 r4 80121.0 r8) v4 v3 v9 v0) q23 q23))))
(assert (or (forall ((q23 Bool)) v0) (exists ((q23 Bool)) (not (not q23)))))
(check-sat-assuming (IP_4 IP_6))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_4))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_6))
(get-unsat-core)
(check-sat-assuming (IP_3 IP_4))
(get-unsat-core)
(check-sat-assuming (IP_3 IP_5))
(get-unsat-core)
(declare-fun r9 () Real)
(assert (not (forall ((q24 Real)) (not (= r9 5651986.0)))))
(check-sat-assuming (IP_1 IP_6))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_4))
(get-unsat-core)
(check-sat-assuming (IP_4 IP_6))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_2))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_3))
(get-unsat-core)
(push 1)
(check-sat)
(check-sat-assuming (IP_1 IP_5))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_4))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_6))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_4))
(get-unsat-core)
(check-sat-assuming (IP_4 IP_6))
(get-unsat-core)
(declare-fun v11 () Bool)
(assert (not (forall ((q25 Bool) (q26 Bool) (q27 Real) (q28 Real)) (not (=> q25 q26)))))
(check-sat-assuming (IP_5 IP_6))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_4))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_3))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_3))
(get-unsat-core)
(check-sat-assuming (IP_4 IP_5))
(get-unsat-core)
(assert (not (exists ((q29 Real)) (not (> q29 q29 q29 q29 r0)))))
(assert (! (distinct v1 (distinct 0.3 r5 80121.0) v4 (<= 90719737.0 r0 r4 52895.0) (<= 90719737.0 r0 r4 52895.0) v9 (> r8 (/ r2 r5) r2 r7 (/ 90719737.0 r5)) v7 v5 (not v3)) :named IP_8))
(check-sat-assuming (IP_4 IP_5))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_3))
(get-unsat-core)
(check-sat-assuming (IP_6 IP_7))
(get-unsat-core)
(check-sat-assuming (IP_3 IP_4))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_4))
(get-unsat-core)
(push 1)
(declare-fun v12 () Bool)
(assert (not (exists ((q30 Real)) (not (< q30 q30)))))
(check-sat-assuming (IP_3 IP_7))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_5))
(get-unsat-core)
(check-sat-assuming (IP_4 IP_5))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_6))
(get-unsat-core)
(check-sat-assuming (IP_6 IP_7))
(get-unsat-core)
(pop 1)
(declare-fun v13 () Bool)
(assert (forall ((q31 Real) (q32 Real) (q33 Real)) (not (= (- 90719737.0 r4 80121.0) q31 q32))))
(check-sat-assuming (IP_4 IP_7))
(get-unsat-core)
(check-sat-assuming (IP_3 IP_6))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_3))
(get-unsat-core)
(check-sat-assuming (IP_3 IP_4))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_4))
(get-unsat-core)
(assert (not (forall ((q34 Real) (q35 Real) (q36 Real)) (not (>= q36 q35 q35)))))
(check-sat-assuming (IP_6 IP_7))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_6))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_4))
(get-unsat-core)
(check-sat-assuming (IP_4 IP_6))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_2))
(get-unsat-core)
(push 1)
(assert (not (exists ((q37 Real) (q38 Real) (q39 Bool) (q40 Real)) (distinct v1 (distinct 0.3 r5 80121.0) v4 (<= 90719737.0 r0 r4 52895.0) (<= 90719737.0 r0 r4 52895.0) v9 (> r8 (/ r2 r5) r2 r7 (/ 90719737.0 r5)) v7 v5 (not v3)))))
(check-sat-assuming (IP_2 IP_4))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_3))
(get-unsat-core)
(check-sat-assuming (IP_3 IP_5))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_7))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_2))
(get-unsat-core)
(pop 1)
(declare-fun v14 () Bool)
(assert (forall ((q41 Bool)) (not (=> v0 q41))))
(assert (! (and v0 (xor (distinct (not v3) v3 v4 (not v3) (<= r7 90719737.0 r4 80121.0 r8) v4 v3 v9 v0) v0 v8 (> r8 (/ r2 r5) r2 r7 (/ 90719737.0 r5)) (not v3) v8 v0 (distinct (<= 90719737.0 r0 r4 52895.0) (not v3) v4) (not v0)) v14 (distinct v1 (distinct 0.3 r5 80121.0) v4 (<= 90719737.0 r0 r4 52895.0) (<= 90719737.0 r0 r4 52895.0) v9 (> r8 (/ r2 r5) r2 r7 (/ 90719737.0 r5)) v7 v5 (not v3)) v11 v7 (not v3) v13 v0 v1 v13) :named IP_9))
(check-sat-assuming (IP_1 IP_3))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_2))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_5))
(get-unsat-core)
(check-sat-assuming (IP_3 IP_8))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_4))
(get-unsat-core)
(assert (! (= v3 v3 (<= 90719737.0 r0 r4 52895.0) v7 (> r8 (/ r2 r5) r2 r7 (/ 90719737.0 r5)) (distinct v10 (<= r7 90719737.0 r4 80121.0 r8) (not v0) (distinct (not v3) v3 v4 (not v3) (<= r7 90719737.0 r4 80121.0 r8) v4 v3 v9 v0) (<= 90719737.0 r0 r4 52895.0) (distinct 0.3 r2 (/ 90719737.0 r5) r4 r8) v9 v9 v2 v10 v8) v3 (distinct v10 (<= r7 90719737.0 r4 80121.0 r8) (not v0) (distinct (not v3) v3 v4 (not v3) (<= r7 90719737.0 r4 80121.0 r8) v4 v3 v9 v0) (<= 90719737.0 r0 r4 52895.0) (distinct 0.3 r2 (/ 90719737.0 r5) r4 r8) v9 v9 v2 v10 v8)) :named IP_10))
(check-sat-assuming (IP_5 IP_8))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_2))
(get-unsat-core)
(check-sat-assuming (IP_5 IP_9))
(get-unsat-core)
(check-sat-assuming (IP_6 IP_8))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_6))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_2))
(get-unsat-core)
(check-sat-assuming (IP_4 IP_7))
(get-unsat-core)
(check-sat-assuming (IP_3 IP_8))
(get-unsat-core)
(check-sat-assuming (IP_4 IP_8))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_3))
(get-unsat-core)
(assert (not (exists ((q42 Bool)) (not (and q42 q42 q42 v4 (distinct 0.3 r2 (/ 90719737.0 r5) r4 r8) q42 q42 (distinct 0.3 r5 80121.0))))))
(assert (! (xor v4 (distinct 0.3 r5 80121.0) (<= 90719737.0 r0 r4 52895.0)) :named IP_11))
(check-sat-assuming (IP_2 IP_9))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_6))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_6))
(get-unsat-core)
(check-sat-assuming (IP_7 IP_9))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_8))
(get-unsat-core)
(declare-fun v15 () Bool)
(check-sat-assuming (IP_3 IP_6))
(get-unsat-core)
(check-sat-assuming (IP_6 IP_9))
(get-unsat-core)
(check-sat-assuming (IP_9 IP_10))
(get-unsat-core)
(check-sat-assuming (IP_3 IP_7))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_9))
(get-unsat-core)
(push 1)
(declare-fun v16 () Bool)
(assert (not (forall ((q43 Real) (q44 Bool) (q45 Bool)) v9)))
(check-sat-assuming (IP_2 IP_5))
(get-unsat-core)
(check-sat-assuming (IP_4 IP_10))
(get-unsat-core)
(check-sat-assuming (IP_4 IP_5))
(get-unsat-core)
(check-sat-assuming (IP_6 IP_10))
(get-unsat-core)
(check-sat-assuming (IP_9 IP_10))
(get-unsat-core)
(assert (! v4 :named IP_12))
(check-sat-assuming (IP_7 IP_8))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_9))
(get-unsat-core)
(check-sat-assuming (IP_4 IP_6))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_8))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_7))
(get-unsat-core)
(declare-fun v17 () Bool)
(assert (exists ((q46 Bool) (q47 Bool) (q48 Real)) (xor v4 (distinct 0.3 r5 80121.0) (<= 90719737.0 r0 r4 52895.0))))
(check-sat-assuming (IP_3 IP_7))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_4))
(get-unsat-core)
(check-sat-assuming (IP_3 IP_4))
(get-unsat-core)
(check-sat-assuming (IP_5 IP_7))
(get-unsat-core)
(check-sat-assuming (IP_7 IP_11))
(get-unsat-core)
(declare-fun r10 () Real)
(assert (exists ((q49 Real)) (<= r7 90719737.0 r4 80121.0 r8)))
(check-sat-assuming (IP_1 IP_5))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_3))
(get-unsat-core)
(check-sat-assuming (IP_9 IP_10))
(get-unsat-core)
(check-sat-assuming (IP_4 IP_7))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_11))
(get-unsat-core)
(assert (exists ((q50 Bool) (q51 Bool)) (not (distinct v16 q51 v8))))
(assert (or (forall ((q50 Bool) (q51 Bool)) (distinct (<= 90719737.0 r0 r4 52895.0) (not v3) v4)) (exists ((q50 Bool) (q51 Bool)) (not (not v3)))))
(check-sat-assuming (IP_4 IP_8))
(get-unsat-core)
(check-sat-assuming (IP_9 IP_11))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_3))
(get-unsat-core)
(check-sat-assuming (IP_3 IP_8))
(get-unsat-core)
(check-sat-assuming (IP_10 IP_11))
(get-unsat-core)
(assert (not (forall ((q52 Real) (q53 Real) (q54 Real) (q55 Bool)) (not (not v15)))))
(check-sat-assuming (IP_3 IP_7))
(get-unsat-core)
(check-sat-assuming (IP_7 IP_8))
(get-unsat-core)
(check-sat-assuming (IP_5 IP_11))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_8))
(get-unsat-core)
(check-sat-assuming (IP_5 IP_8))
(get-unsat-core)
(assert (exists ((q56 Real) (q57 Real)) (not (> r4 q57 (/ r9 90719737.0) r2 90719737.0))))
(assert (exists ((q56 Real) ) (forall ((q57 Real) ) v14)))
(check-sat-assuming (IP_2 IP_3))
(get-unsat-core)
(check-sat-assuming (IP_3 IP_10))
(get-unsat-core)
(check-sat-assuming (IP_6 IP_10))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_5))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_11))
(get-unsat-core)
(push 1)
(assert (exists ((q58 Real) (q59 Bool) (q60 Bool)) (=> (> q58 q58) (distinct q59 (>= (/ r5 r0) r0) q59))))
(assert (! (<= r7 90719737.0 r4 80121.0 r8) :named IP_13))
(check-sat-assuming (IP_1 IP_5))
(get-unsat-core)
(check-sat-assuming (IP_5 IP_9))
(get-unsat-core)
(check-sat-assuming (IP_6 IP_10))
(get-unsat-core)
(check-sat-assuming (IP_7 IP_10))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_4))
(get-unsat-core)
(push 1)
(assert (exists ((q61 Real) (q62 Bool)) (=> (= q62 (not v0) v4 q62 (distinct v1 (distinct 0.3 r5 80121.0) v4 (<= 90719737.0 r0 r4 52895.0) (<= 90719737.0 r0 r4 52895.0) v9 (> r8 (/ r2 r5) r2 r7 (/ 90719737.0 r5)) v7 v5 (not v3)) v7 q62 q62 q62) (= r5 80121.0))))
(assert (! v4 :named IP_14))
(check-sat-assuming (IP_5 IP_9))
(get-unsat-core)
(check-sat-assuming (IP_3 IP_10))
(get-unsat-core)
(check-sat-assuming (IP_4 IP_13))
(get-unsat-core)
(check-sat-assuming (IP_6 IP_7))
(get-unsat-core)
(check-sat-assuming (IP_3 IP_7))
(get-unsat-core)
(assert (forall ((q63 Real) (q64 Bool) (q65 Bool)) (=> (< q63 q63 q63) (or (not v3) q64 q64))))
(assert (! (or (distinct v1 (distinct 0.3 r5 80121.0) v4 (<= 90719737.0 r0 r4 52895.0) (<= 90719737.0 r0 r4 52895.0) v9 (> r8 (/ r2 r5) r2 r7 (/ 90719737.0 r5)) v7 v5 (not v3)) v16 v9 v14 (distinct v1 (distinct 0.3 r5 80121.0) v4 (<= 90719737.0 r0 r4 52895.0) (<= 90719737.0 r0 r4 52895.0) v9 (> r8 (/ r2 r5) r2 r7 (/ 90719737.0 r5)) v7 v5 (not v3)) (and v0 (xor (distinct (not v3) v3 v4 (not v3) (<= r7 90719737.0 r4 80121.0 r8) v4 v3 v9 v0) v0 v8 (> r8 (/ r2 r5) r2 r7 (/ 90719737.0 r5)) (not v3) v8 v0 (distinct (<= 90719737.0 r0 r4 52895.0) (not v3) v4) (not v0)) v14 (distinct v1 (distinct 0.3 r5 80121.0) v4 (<= 90719737.0 r0 r4 52895.0) (<= 90719737.0 r0 r4 52895.0) v9 (> r8 (/ r2 r5) r2 r7 (/ 90719737.0 r5)) v7 v5 (not v3)) v11 v7 (not v3) v13 v0 v1 v13)) :named IP_15))
(check-sat-assuming (IP_1 IP_12))
(get-unsat-core)
(check-sat-assuming (IP_6 IP_14))
(get-unsat-core)
(check-sat-assuming (IP_3 IP_7))
(get-unsat-core)
(check-sat-assuming (IP_10 IP_11))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_7))
(get-unsat-core)
(assert (not (exists ((q66 Bool) (q67 Real) (q68 Real) (q69 Real)) v2)))
(assert (! (or (< 5651986.0 r7 52895.0 90719737.0) v10) :named IP_16))
(check-sat-assuming (IP_2 IP_3))
(get-unsat-core)
(check-sat-assuming (IP_3 IP_15))
(get-unsat-core)
(check-sat-assuming (IP_4 IP_7))
(get-unsat-core)
(check-sat-assuming (IP_7 IP_9))
(get-unsat-core)
(check-sat-assuming (IP_8 IP_9))
(get-unsat-core)
(declare-fun v18 () Bool)
(assert (not (exists ((q70 Bool) (q71 Real) (q72 Real) (q73 Real)) (distinct (<= 90719737.0 r0 r4 52895.0) (not v3) v4))))
(check-sat-assuming (IP_4 IP_10))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_15))
(get-unsat-core)
(check-sat-assuming (IP_11 IP_13))
(get-unsat-core)
(check-sat-assuming (IP_6 IP_13))
(get-unsat-core)
(check-sat-assuming (IP_5 IP_10))
(get-unsat-core)
(push 1)
(declare-fun v19 () Bool)
(check-sat-assuming (IP_5 IP_7))
(get-unsat-core)
(check-sat-assuming (IP_3 IP_4))
(get-unsat-core)
(check-sat-assuming (IP_10 IP_15))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_13))
(get-unsat-core)
(check-sat-assuming (IP_4 IP_9))
(get-unsat-core)
(assert (exists ((q74 Bool) (q75 Bool) (q76 Bool)) v13))
(check-sat-assuming (IP_2 IP_9))
(get-unsat-core)
(check-sat-assuming (IP_10 IP_15))
(get-unsat-core)
(check-sat-assuming (IP_4 IP_7))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_5))
(get-unsat-core)
(check-sat-assuming (IP_10 IP_12))
(get-unsat-core)
(assert (! (xor (distinct (not v3) v3 v4 (not v3) (<= r7 90719737.0 r4 80121.0 r8) v4 v3 v9 v0) v0 v8 (> r8 (/ r2 r5) r2 r7 (/ 90719737.0 r5)) (not v3) v8 v0 (distinct (<= 90719737.0 r0 r4 52895.0) (not v3) v4) (not v0)) :named IP_17))
(check-sat-assuming (IP_3 IP_6))
(get-unsat-core)
(check-sat-assuming (IP_6 IP_14))
(get-unsat-core)
(check-sat-assuming (IP_10 IP_11))
(get-unsat-core)
(check-sat-assuming (IP_11 IP_16))
(get-unsat-core)
(check-sat-assuming (IP_7 IP_10))
(get-unsat-core)
(declare-fun v20 () Bool)
(assert (not (forall ((q77 Bool)) (distinct (not v3) v3 v4 (not v3) (<= r7 90719737.0 r4 80121.0 r8) v4 v3 v9 v0))))
(check-sat-assuming (IP_3 IP_16))
(get-unsat-core)
(check-sat-assuming (IP_5 IP_7))
(get-unsat-core)
(check-sat-assuming (IP_4 IP_16))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_7))
(get-unsat-core)
(check-sat-assuming (IP_10 IP_13))
(get-unsat-core)
(declare-fun r11 () Real)
(assert (not (exists ((q78 Real) (q79 Real)) (= v3 v3 (<= 90719737.0 r0 r4 52895.0) v7 (> r8 (/ r2 r5) r2 r7 (/ 90719737.0 r5)) (distinct v10 (<= r7 90719737.0 r4 80121.0 r8) (not v0) (distinct (not v3) v3 v4 (not v3) (<= r7 90719737.0 r4 80121.0 r8) v4 v3 v9 v0) (<= 90719737.0 r0 r4 52895.0) (distinct 0.3 r2 (/ 90719737.0 r5) r4 r8) v9 v9 v2 v10 v8) v3 (distinct v10 (<= r7 90719737.0 r4 80121.0 r8) (not v0) (distinct (not v3) v3 v4 (not v3) (<= r7 90719737.0 r4 80121.0 r8) v4 v3 v9 v0) (<= 90719737.0 r0 r4 52895.0) (distinct 0.3 r2 (/ 90719737.0 r5) r4 r8) v9 v9 v2 v10 v8)))))
(assert (! (= (distinct (>= (/ r5 r0) r0) (distinct (not v3) v3 v4 (not v3) (<= r7 90719737.0 r4 80121.0 r8) v4 v3 v9 v0) v5 (> r8 (/ r2 r5) r2 r7 (/ 90719737.0 r5)) (not v3) (=> v4 (>= r7 52895.0 r4)) (<= 90719737.0 r0 r4 52895.0) (< 5651986.0 r7 52895.0 90719737.0) v14 v15 (distinct 0.3 r5 80121.0)) v9 (=> v4 (>= r7 52895.0 r4)) v9 (distinct 0.3 r5 80121.0) (and v0 (xor (distinct (not v3) v3 v4 (not v3) (<= r7 90719737.0 r4 80121.0 r8) v4 v3 v9 v0) v0 v8 (> r8 (/ r2 r5) r2 r7 (/ 90719737.0 r5)) (not v3) v8 v0 (distinct (<= 90719737.0 r0 r4 52895.0) (not v3) v4) (not v0)) v14 (distinct v1 (distinct 0.3 r5 80121.0) v4 (<= 90719737.0 r0 r4 52895.0) (<= 90719737.0 r0 r4 52895.0) v9 (> r8 (/ r2 r5) r2 r7 (/ 90719737.0 r5)) v7 v5 (not v3)) v11 v7 (not v3) v13 v0 v1 v13)) :named IP_18))
(check-sat-assuming (IP_1 IP_9))
(get-unsat-core)
(check-sat-assuming (IP_5 IP_11))
(get-unsat-core)
(check-sat-assuming (IP_8 IP_16))
(get-unsat-core)
(check-sat-assuming (IP_4 IP_12))
(get-unsat-core)
(check-sat-assuming (IP_10 IP_16))
(get-unsat-core)
(declare-fun v21 () Bool)
(assert (not (exists ((q80 Real) (q81 Real) (q82 Bool) (q83 Real)) (and v8 v8 v13 v2 (<= 90719737.0 r0 r4 52895.0) v0 (<= 90719737.0 r0 r4 52895.0)))))
(check-sat)
(check-sat-assuming (IP_14 IP_17))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_15))
(get-unsat-core)
(check-sat-assuming (IP_10 IP_15))
(get-unsat-core)
(check-sat-assuming (IP_5 IP_12))
(get-unsat-core)
(check-sat-assuming (IP_3 IP_13))
(get-unsat-core)
(declare-fun v22 () Bool)
(assert (exists ((q84 Real) (q85 Real)) (or (< 5651986.0 r7 52895.0 90719737.0) v10)))
(check-sat-assuming (IP_9 IP_17))
(get-unsat-core)
(check-sat-assuming (IP_5 IP_14))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_5))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_2))
(get-unsat-core)
(check-sat-assuming (IP_3 IP_10))
(get-unsat-core)
(assert (not (forall ((q86 Real) (q87 Bool) (q88 Real) (q89 Bool)) (< (/ 90719737.0 r5) r4))))
(check-sat-assuming (IP_4 IP_17))
(get-unsat-core)
(check-sat-assuming (IP_9 IP_12))
(get-unsat-core)
(check-sat-assuming (IP_16 IP_17))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_10))
(get-unsat-core)
(check-sat-assuming (IP_11 IP_17))
(get-unsat-core)
(assert (not (forall ((q90 Real) (q91 Real) (q92 Bool)) (distinct (<= 90719737.0 r0 r4 52895.0) (not v3) v4))))
(check-sat-assuming (IP_6 IP_17))
(get-unsat-core)
(check-sat-assuming (IP_9 IP_17))
(get-unsat-core)
(check-sat-assuming (IP_8 IP_17))
(get-unsat-core)
(check-sat-assuming (IP_3 IP_17))
(get-unsat-core)
(check-sat-assuming (IP_13 IP_14))
(get-unsat-core)
(assert (! (distinct (/ r9 r8) r10 r8 r2 (/ r5 r0)) :named IP_19))
(check-sat-assuming (IP_8 IP_15))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_5))
(get-unsat-core)
(check-sat-assuming (IP_11 IP_16))
(get-unsat-core)
(check-sat-assuming (IP_14 IP_15))
(get-unsat-core)
(check-sat-assuming (IP_4 IP_15))
(get-unsat-core)
(assert (not (exists ((q93 Real)) (not (distinct q93 q93 r11 q93 (* r2 r4 r8 (/ r2 r5) r0))))))
(assert (! (xor v13 v3 v15 (= (distinct 0.3 r5 80121.0) v2 (<= r7 90719737.0 r4 80121.0 r8) v13 v10 (and v0 (xor (distinct (not v3) v3 v4 (not v3) (<= r7 90719737.0 r4 80121.0 r8) v4 v3 v9 v0) v0 v8 (> r8 (/ r2 r5) r2 r7 (/ 90719737.0 r5)) (not v3) v8 v0 (distinct (<= 90719737.0 r0 r4 52895.0) (not v3) v4) (not v0)) v14 (distinct v1 (distinct 0.3 r5 80121.0) v4 (<= 90719737.0 r0 r4 52895.0) (<= 90719737.0 r0 r4 52895.0) v9 (> r8 (/ r2 r5) r2 r7 (/ 90719737.0 r5)) v7 v5 (not v3)) v11 v7 (not v3) v13 v0 v1 v13) (distinct (not v3) v3 v4 (not v3) (<= r7 90719737.0 r4 80121.0 r8) v4 v3 v9 v0) v13) (<= 90719737.0 r0 r4 52895.0) v14 (=> v4 (>= r7 52895.0 r4)) (not v0)) :named IP_20))
(check-sat-assuming (IP_1 IP_15))
(get-unsat-core)
(check-sat-assuming (IP_10 IP_15))
(get-unsat-core)
(check-sat-assuming (IP_8 IP_16))
(get-unsat-core)
(check-sat-assuming (IP_3 IP_12))
(get-unsat-core)
(check-sat-assuming (IP_8 IP_15))
(get-unsat-core)
(check-sat)
(get-unsat-core)
(check-sat-assuming (IP_6 IP_9))
(get-unsat-core)
(check-sat-assuming (IP_6 IP_19))
(get-unsat-core)
(check-sat-assuming (IP_5 IP_17))
(get-unsat-core)
(check-sat-assuming (IP_10 IP_11))
(get-unsat-core)
(check-sat-assuming (IP_14 IP_19))
(get-unsat-core)
(check-sat-assuming (IP_8 IP_14))
(get-unsat-core)
(check-sat-assuming (IP_2 IP_11))
(get-unsat-core)
(check-sat-assuming (IP_1 IP_18))
(get-unsat-core)
(check-sat-assuming (IP_11 IP_15))
(get-unsat-core)
(check-sat-assuming (IP_11 IP_18))
(get-unsat-core)
(exit)
