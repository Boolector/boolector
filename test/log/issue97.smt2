(set-logic BV)
(declare-const bv_3-0 (_ BitVec 3))
(assert (not (forall ((q13 (_ BitVec 3))) (not (= bv_3-0 q13 (bvsdiv bv_3-0 (_ bv0 3)) q13 bv_3-0)))))
(check-sat)
