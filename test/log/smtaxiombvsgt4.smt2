
(set-logic QF_BV)
(declare-fun s () (_ BitVec 4))
(declare-fun t () (_ BitVec 4))
(assert (not (= (bvsgt s t) (bvslt t s))))
(check-sat)
(exit)
