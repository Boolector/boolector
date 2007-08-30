(benchmark smtaxiombvxor
 :logic QF_BV
 :extrafuns ((s BitVec[7]))
 :extrafuns ((t BitVec[7]))
 :formula (not (=
    (bvxor s t)  (bvor (bvand s (bvnot t)) (bvand (bvnot s) t))
)))
