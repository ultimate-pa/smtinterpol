(set-logic LIA) 
(declare-fun v4 () Bool)
(declare-fun v7 () Bool)
(declare-fun v10 () Bool)
(assert (not (exists ((q0 Bool) (q1 Int) (q2 Bool) (q3 Int)) (not (>= 6 q3)))))
(push 1)
(assert (xor v7 v10 (= v4 v7 ) v4 (not v10)))
(pop 1)
(check-sat)

