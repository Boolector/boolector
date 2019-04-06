(benchmark bvlshr1
 :logic QF_BV
 :assumption (= (bvlshr bv0[1] bv0[1]) bv0[1])
 :assumption (= (bvlshr bv0[1] bv1[1]) bv0[1])
 :assumption (= (bvlshr bv1[1] bv0[1]) bv1[1])
 :assumption (= (bvlshr bv1[1] bv1[1]) bv0[1])
 :formula true)
