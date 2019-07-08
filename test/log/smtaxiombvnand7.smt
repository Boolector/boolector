(benchmark smtaxiombvnand
 :logic QF_BV
 :extrafuns ((s BitVec[7]))
 :extrafuns ((t BitVec[7]))
 :formula (not (=
    (bvnand s t)  (bvnot (bvand s t))
)))
