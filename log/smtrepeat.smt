(benchmark smtrepeat
 :logic QF_BV
 :assumption (= (repeat[3] bit0) bvbin000)
 :assumption (= (repeat[4] bv10[4]) bvhexaaaa)
 :formula true)
