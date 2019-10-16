(set-option :incremental false)
(set-logic QF_BV)
(declare-fun s () (_ BitVec 5))
(declare-fun t () (_ BitVec 5))

(assert (not (= (bvsub s t) (bvadd s (bvneg t)))))



