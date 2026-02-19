; Hey ChatGPT, can you refute x*x < 0 ?
(set-logic QF_NRA)
(declare-fun x () Real)
(assert (< (* x x) 0.0))
(check-sat)
(get-proof)
