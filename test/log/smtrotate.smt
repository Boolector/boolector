(benchmark smtrotate
 :logic QF_BV

 :assumption (= (rotate_left[0] bv3[4]) bv3[4])
 :assumption (= (rotate_left[1] bv3[4]) bv6[4])
 :assumption (= (rotate_left[2] bv3[4]) bv12[4])
 :assumption (= (rotate_left[3] bv3[4]) bv9[4])
 :assumption (= (rotate_left[4] bv3[4]) bv3[4])
 :assumption (= (rotate_left[5] bv3[4]) bv6[4])
 :assumption (= (rotate_left[6] bv3[4]) bv12[4])
 :assumption (= (rotate_left[7] bv3[4]) bv9[4])

 :assumption (= (rotate_right[0] bv3[4]) bv3[4])
 :assumption (= (rotate_right[1] bv3[4]) bv9[4])
 :assumption (= (rotate_right[2] bv3[4]) bv12[4])
 :assumption (= (rotate_right[3] bv3[4]) bv6[4])
 :assumption (= (rotate_right[4] bv3[4]) bv3[4])
 :assumption (= (rotate_right[5] bv3[4]) bv9[4])
 :assumption (= (rotate_right[6] bv3[4]) bv12[4])
 :assumption (= (rotate_right[7] bv3[4]) bv6[4])

 :formula true)
