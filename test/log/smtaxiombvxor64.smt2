
(set-logic QF_BV)
(declare-fun s () (_ BitVec 64))
(declare-fun t () (_ BitVec 64))
(assert (not (= (bvxor s t) (bvor (bvand s (bvnot t)) (bvand (bvnot s) t)))))
(check-sat)
(exit)
