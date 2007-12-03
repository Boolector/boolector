(benchmark bvashr1
 :logic QF_BV
 :assumption (= (bvashr bv0[1] bv0[1]) bv0[1])
 :assumption (= (bvashr bv0[1] bv1[1]) bv0[1])
 :assumption (= (bvashr bv1[1] bv0[1]) bv1[1])
 :assumption (= (bvashr bv1[1] bv1[1]) bv1[1])
 :formula true)
