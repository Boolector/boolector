(benchmark smtaxiombvnor
 :logic QF_BV
 :extrafuns ((s BitVec[5]))
 :extrafuns ((t BitVec[5]))
 :formula (not (=
    (bvnor s t)  (bvnot (bvor s t))
)))
