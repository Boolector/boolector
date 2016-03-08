(benchmark smtaxiombvnand
 :logic QF_BV
 :extrafuns ((s BitVec[3]))
 :extrafuns ((t BitVec[3]))
 :formula (not (=
    (bvnand s t)  (bvnot (bvand s t))
)))
