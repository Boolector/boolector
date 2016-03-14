(benchmark smtaxiombvnand
 :logic QF_BV
 :extrafuns ((s BitVec[5]))
 :extrafuns ((t BitVec[5]))
 :formula (not (=
    (bvnand s t)  (bvnot (bvand s t))
)))
