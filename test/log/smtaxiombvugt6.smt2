
(set-logic QF_BV)
(declare-fun s () (_ BitVec 6))
(declare-fun t () (_ BitVec 6))
(assert (not (= (bvugt s t) (bvult t s))))
(check-sat)
(exit)
