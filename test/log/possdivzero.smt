(benchmark possdivzero
 :logic QF_BV
 :extrafuns ((s BitVec[4]))
 :assumption (bvsge s bv0[4])
 :formula (not (= (bvsdiv s bv0[4]) (bvnot bv0[4]))))
