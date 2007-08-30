(benchmark smtaxiombvnand
 :logic QF_BV
 :extrafuns ((s BitVec[32]))
 :extrafuns ((t BitVec[32]))
 :formula (not (=
    (bvnand s t)  (bvnot (bvand s t))
)))
