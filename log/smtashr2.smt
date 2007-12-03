(benchmark bvashr2
 :logic QF_BV

 :assumption (= (bvashr bv0[2] bv0[2]) bv0[2])
 :assumption (= (bvashr bv0[2] bv1[2]) bv0[2])
 :assumption (= (bvashr bv0[2] bv2[2]) bv0[2])
 :assumption (= (bvashr bv0[2] bv3[2]) bv0[2])

 :assumption (= (bvashr bv1[2] bv0[2]) bv1[2])
 :assumption (= (bvashr bv1[2] bv1[2]) bv0[2])
 :assumption (= (bvashr bv1[2] bv2[2]) bv0[2])
 :assumption (= (bvashr bv1[2] bv3[2]) bv0[2])

 :assumption (= (bvashr bv2[2] bv0[2]) bv2[2])
 :assumption (= (bvashr bv2[2] bv1[2]) bv3[2])
 :assumption (= (bvashr bv2[2] bv2[2]) bv3[2])
 :assumption (= (bvashr bv2[2] bv3[2]) bv3[2])

 :assumption (= (bvashr bv3[2] bv0[2]) bv3[2])
 :assumption (= (bvashr bv3[2] bv1[2]) bv3[2])
 :assumption (= (bvashr bv3[2] bv2[2]) bv3[2])
 :assumption (= (bvashr bv3[2] bv3[2]) bv3[2])

 :formula true)
