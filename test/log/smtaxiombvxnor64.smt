(benchmark smtaxiombvxnor
 :logic QF_BV
 :extrafuns ((s BitVec[64]))
 :extrafuns ((t BitVec[64]))
 :formula (not (=
    (bvxnor s t)  (bvor (bvand s t) (bvand (bvnot s) (bvnot t)))
)))
