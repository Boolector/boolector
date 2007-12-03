(benchmark bvlshr2
 :logic QF_BV

 :assumption (= (bvlshr bv0[2] bv0[2]) bv0[2])
 :assumption (= (bvlshr bv0[2] bv1[2]) bv0[2])
 :assumption (= (bvlshr bv0[2] bv2[2]) bv0[2])
 :assumption (= (bvlshr bv0[2] bv3[2]) bv0[2])

 :assumption (= (bvlshr bv1[2] bv0[2]) bv1[2])
 :assumption (= (bvlshr bv1[2] bv1[2]) bv0[2])
 :assumption (= (bvlshr bv1[2] bv2[2]) bv0[2])
 :assumption (= (bvlshr bv1[2] bv3[2]) bv0[2])

 :assumption (= (bvlshr bv2[2] bv0[2]) bv2[2])
 :assumption (= (bvlshr bv2[2] bv1[2]) bv1[2])
 :assumption (= (bvlshr bv2[2] bv2[2]) bv0[2])
 :assumption (= (bvlshr bv2[2] bv3[2]) bv0[2])

 :assumption (= (bvlshr bv3[2] bv0[2]) bv3[2])
 :assumption (= (bvlshr bv3[2] bv1[2]) bv1[2])
 :assumption (= (bvlshr bv3[2] bv2[2]) bv0[2])
 :assumption (= (bvlshr bv3[2] bv3[2]) bv0[2])

 :formula true)
