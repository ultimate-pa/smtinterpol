(set-logic NRA)
(declare-fun v0 () Bool)
(declare-fun v1 () Bool)
(declare-fun v2 () Bool)
(declare-fun v3 () Bool)
(declare-fun v4 () Bool)
(declare-fun v5 () Bool)
(declare-fun v6 () Bool)
(declare-fun v7 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(assert (not v3))
(check-sat)
(assert (or (>= r1 r2 r0) (>= r1 r2 r0) v5 v2 v2))
(declare-fun v10 () Bool)
(declare-fun v11 () Bool)
(assert (not (exists ((q3 Bool) (q4 Bool) (q5 Real) (q6 Bool)) (=> (>= q5 r1) (xor q4 q3 q3 v10 v11 q3 (or v4 (xor v7 v5 v7) v3 v5 v3 (not v3) v7 v4 v10))))))
(push 1)
(push 1)
(check-sat)
(pop 1)
(push 1)
(check-sat)

