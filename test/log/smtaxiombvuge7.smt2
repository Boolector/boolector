
(set-logic QF_BV)
(declare-fun s () (_ BitVec 7))
(declare-fun t () (_ BitVec 7))
(assert (not (= (bvuge s t) (or (bvult t s) (= s t)))))
(check-sat)
(exit)
