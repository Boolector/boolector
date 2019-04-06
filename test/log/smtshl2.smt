(benchmark bvshl2
 :logic QF_BV

 :assumption (= (bvshl bv0[2] bv0[2]) bv0[2])
 :assumption (= (bvshl bv0[2] bv1[2]) bv0[2])
 :assumption (= (bvshl bv0[2] bv2[2]) bv0[2])
 :assumption (= (bvshl bv0[2] bv3[2]) bv0[2])

 :assumption (= (bvshl bv1[2] bv0[2]) bv1[2])
 :assumption (= (bvshl bv1[2] bv1[2]) bv2[2])
 :assumption (= (bvshl bv1[2] bv2[2]) bv0[2])
 :assumption (= (bvshl bv1[2] bv3[2]) bv0[2])

 :assumption (= (bvshl bv2[2] bv0[2]) bv2[2])
 :assumption (= (bvshl bv2[2] bv1[2]) bv0[2])
 :assumption (= (bvshl bv2[2] bv2[2]) bv0[2])
 :assumption (= (bvshl bv2[2] bv3[2]) bv0[2])

 :assumption (= (bvshl bv3[2] bv0[2]) bv3[2])
 :assumption (= (bvshl bv3[2] bv1[2]) bv2[2])
 :assumption (= (bvshl bv3[2] bv2[2]) bv0[2])
 :assumption (= (bvshl bv3[2] bv3[2]) bv0[2])

 :formula true)
