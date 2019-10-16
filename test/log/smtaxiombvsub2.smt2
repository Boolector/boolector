(set-option :incremental false)
(set-logic QF_BV)
(declare-fun s () (_ BitVec 2))
(declare-fun t () (_ BitVec 2))

(assert (not (= (bvsub s t) (bvadd s (bvneg t)))))



