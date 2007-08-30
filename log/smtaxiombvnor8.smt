(benchmark smtaxiombvnor
 :logic QF_BV
 :extrafuns ((s BitVec[8]))
 :extrafuns ((t BitVec[8]))
 :formula (not (=
    (bvnor s t)  (bvnot (bvor s t))
)))
