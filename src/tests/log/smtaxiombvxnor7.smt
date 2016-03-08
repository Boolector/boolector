(benchmark smtaxiombvxnor
 :logic QF_BV
 :extrafuns ((s BitVec[7]))
 :extrafuns ((t BitVec[7]))
 :formula (not (=
    (bvxnor s t)  (bvor (bvand s t) (bvand (bvnot s) (bvnot t)))
)))
