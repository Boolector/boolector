(set-option :incremental false)
(set-logic QF_BV)
(declare-fun s () (_ BitVec 2))
(declare-fun t () (_ BitVec 2))

(assert (not (= (bvsge s t) (bvsle t s))))



