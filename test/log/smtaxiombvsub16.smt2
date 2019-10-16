(set-option :incremental false)
(set-logic QF_BV)
(declare-fun s () (_ BitVec 16))
(declare-fun t () (_ BitVec 16))

(assert (not (= (bvsub s t) (bvadd s (bvneg t)))))



