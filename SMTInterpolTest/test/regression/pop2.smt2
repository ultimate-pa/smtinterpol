(set-logic LIA)
(push)
(declare-fun b () Int)
(assert (exists ((e Int)) (= b e)))
(push)
(push)
(pop)
(pop)
(push)
(assert (< 0 b))
(pop 2)
