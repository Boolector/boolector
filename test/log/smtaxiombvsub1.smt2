
(set-logic QF_BV)
(declare-fun s () (_ BitVec 1))
(declare-fun t () (_ BitVec 1))
(assert (not (= (bvsub s t) (bvadd s (bvneg t)))))
(check-sat)
(exit)
