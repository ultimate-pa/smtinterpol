(set-option :model-check-mode true)
(set-logic QF_AUFLIRA)
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun r () Bool)
(assert (and (and r (or p q)) (not (or p q))))
(check-sat)
