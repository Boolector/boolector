(benchmark smtaxiombvnand
 :logic QF_BV
 :extrafuns ((s BitVec[6]))
 :extrafuns ((t BitVec[6]))
 :formula (not (=
    (bvnand s t)  (bvnot (bvand s t))
)))
