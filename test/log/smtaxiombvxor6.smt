(benchmark smtaxiombvxor
 :logic QF_BV
 :extrafuns ((s BitVec[6]))
 :extrafuns ((t BitVec[6]))
 :formula (not (=
    (bvxor s t)  (bvor (bvand s (bvnot t)) (bvand (bvnot s) t))
)))
