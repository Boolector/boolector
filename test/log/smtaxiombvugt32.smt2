
(set-logic QF_BV)
(declare-fun s () (_ BitVec 32))
(declare-fun t () (_ BitVec 32))
(assert (not (= (bvugt s t) (bvult t s))))
(check-sat)
(exit)
