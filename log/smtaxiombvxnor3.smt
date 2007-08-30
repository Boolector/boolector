(benchmark smtaxiombvxnor
 :logic QF_BV
 :extrafuns ((s BitVec[3]))
 :extrafuns ((t BitVec[3]))
 :formula (not (=
    (bvxnor s t)  (bvor (bvand s t) (bvand (bvnot s) (bvnot t)))
)))
