
(set-logic QF_BV)
(declare-fun s () (_ BitVec 1))
(declare-fun t () (_ BitVec 1))
(assert (not (= (bvuge s t) (or (bvult t s) (= s t)))))
(check-sat)
(exit)
