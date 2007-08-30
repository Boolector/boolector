(benchmark smtaxiombvnand
 :logic QF_BV
 :extrafuns ((s BitVec[2]))
 :extrafuns ((t BitVec[2]))
 :formula (not (=
    (bvnand s t)  (bvnot (bvand s t))
)))
