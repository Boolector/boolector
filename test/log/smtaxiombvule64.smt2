(set-option :incremental false)
(set-logic QF_BV)
(declare-fun s () (_ BitVec 64))
(declare-fun t () (_ BitVec 64))

(assert (not (= (bvule s t) (or (bvult s t) (= s t)))))



