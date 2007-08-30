(benchmark smtaxiombvnand
 :logic QF_BV
 :extrafuns ((s BitVec[1]))
 :extrafuns ((t BitVec[1]))
 :formula (not (=
    (bvnand s t)  (bvnot (bvand s t))
)))
