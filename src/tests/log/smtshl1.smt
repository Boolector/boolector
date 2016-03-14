(benchmark bvshl1
 :logic QF_BV
 :assumption (= (bvshl bv0[1] bv0[1]) bv0[1])
 :assumption (= (bvshl bv0[1] bv1[1]) bv0[1])
 :assumption (= (bvshl bv1[1] bv0[1]) bv1[1])
 :assumption (= (bvshl bv1[1] bv1[1]) bv0[1])
 :formula true)
