(benchmark smtrotate
 :logic QF_BV

 :assumption (= (rotate_left[0] bvbin0011) bvbin0011)
 :assumption (= (rotate_left[1] bvbin0011) bvbin0110)
 :assumption (= (rotate_left[2] bvbin0011) bvbin1100)
 :assumption (= (rotate_left[3] bvbin0011) bvbin1001)
 :assumption (= (rotate_left[4] bvbin0011) bvbin0011)
 :assumption (= (rotate_left[5] bvbin0011) bvbin0110)
 :assumption (= (rotate_left[6] bvbin0011) bvbin1100)
 :assumption (= (rotate_left[7] bvbin0011) bvbin1001)

 :assumption (= (rotate_right[0] bvbin0011) bvbin0011)
 :assumption (= (rotate_right[1] bvbin0011) bvbin1001)
 :assumption (= (rotate_right[2] bvbin0011) bvbin1100)
 :assumption (= (rotate_right[3] bvbin0011) bvbin0110)
 :assumption (= (rotate_right[4] bvbin0011) bvbin0011)
 :assumption (= (rotate_right[5] bvbin0011) bvbin1001)
 :assumption (= (rotate_right[6] bvbin0011) bvbin1100)
 :assumption (= (rotate_right[7] bvbin0011) bvbin0110)

 :formula true)
