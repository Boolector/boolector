(benchmark smtaxiombvxnor
 :logic QF_BV
 :extrafuns ((s BitVec[1]))
 :extrafuns ((t BitVec[1]))
 :formula (not (=
    (bvxnor s t)  (bvor (bvand s t) (bvand (bvnot s) (bvnot t)))
)))
