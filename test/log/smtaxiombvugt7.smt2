
(set-logic QF_BV)
(declare-fun s () (_ BitVec 7))
(declare-fun t () (_ BitVec 7))
(assert (not (= (bvugt s t) (bvult t s))))
(check-sat)
(exit)
