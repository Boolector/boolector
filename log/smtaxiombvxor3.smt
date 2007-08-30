(benchmark smtaxiombvxor
 :logic QF_BV
 :extrafuns ((s BitVec[3]))
 :extrafuns ((t BitVec[3]))
 :formula (not (=
    (bvxor s t)  (bvor (bvand s (bvnot t)) (bvand (bvnot s) t))
)))
