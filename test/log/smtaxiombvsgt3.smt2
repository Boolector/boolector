(set-option :incremental false)
(set-logic QF_BV)
(declare-fun s () (_ BitVec 3))
(declare-fun t () (_ BitVec 3))

(assert (not (= (bvsgt s t) (bvslt t s))))



