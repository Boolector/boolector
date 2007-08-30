(benchmark smtaxiombvxnor
 :logic QF_BV
 :extrafuns ((s BitVec[5]))
 :extrafuns ((t BitVec[5]))
 :formula (not (=
    (bvxnor s t)  (bvor (bvand s t) (bvand (bvnot s) (bvnot t)))
)))
