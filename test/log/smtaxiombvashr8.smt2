(set-option :incremental false)
(set-logic QF_BV)
(declare-fun s () (_ BitVec 8))
(declare-fun t () (_ BitVec 8))

(assert (not (= (bvashr s t) (ite (= ((_ extract 7 7) s) (_ bv0 1)) (bvlshr s t) (bvnot (bvlshr (bvnot s) t))))))



