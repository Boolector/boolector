
(set-logic QF_BV)
(declare-fun s () (_ BitVec 5))
(declare-fun t () (_ BitVec 5))
(assert (not (= (bvsgt s t) (bvslt t s))))
(check-sat)
(exit)
