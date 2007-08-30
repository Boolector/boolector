(benchmark smtaxiombvnor
 :logic QF_BV
 :extrafuns ((s BitVec[2]))
 :extrafuns ((t BitVec[2]))
 :formula (not (=
    (bvnor s t)  (bvnot (bvor s t))
)))
