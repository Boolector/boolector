
(set-logic QF_BV)
(declare-fun s () (_ BitVec 6))
(declare-fun t () (_ BitVec 6))
(assert (not (= (bvsge s t) (bvsle t s))))
(check-sat)
(exit)
