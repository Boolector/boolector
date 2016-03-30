(benchmark smtaxiombvnor
 :logic QF_BV
 :extrafuns ((s BitVec[64]))
 :extrafuns ((t BitVec[64]))
 :formula (not (=
    (bvnor s t)  (bvnot (bvor s t))
)))
