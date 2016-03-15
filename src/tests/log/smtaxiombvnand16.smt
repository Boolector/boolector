(benchmark smtaxiombvnand
 :logic QF_BV
 :extrafuns ((s BitVec[16]))
 :extrafuns ((t BitVec[16]))
 :formula (not (=
    (bvnand s t)  (bvnot (bvand s t))
)))
