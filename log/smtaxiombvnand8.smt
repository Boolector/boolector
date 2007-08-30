(benchmark smtaxiombvnand
 :logic QF_BV
 :extrafuns ((s BitVec[8]))
 :extrafuns ((t BitVec[8]))
 :formula (not (=
    (bvnand s t)  (bvnot (bvand s t))
)))
