(benchmark negsdivzero
 :logic QF_BV
 :extrafuns ((s BitVec[4]))
 :assumption (bvslt s bv0[4])
 :formula (not (= (bvsdiv s bv0[4]) bv1[4])))
