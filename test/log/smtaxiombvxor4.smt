(benchmark smtaxiombvxor
 :logic QF_BV
 :extrafuns ((s BitVec[4]))
 :extrafuns ((t BitVec[4]))
 :formula (not (=
    (bvxor s t)  (bvor (bvand s (bvnot t)) (bvand (bvnot s) t))
)))
