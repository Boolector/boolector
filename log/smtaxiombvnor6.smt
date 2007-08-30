(benchmark smtaxiombvnor
 :logic QF_BV
 :extrafuns ((s BitVec[6]))
 :extrafuns ((t BitVec[6]))
 :formula (not (=
    (bvnor s t)  (bvnot (bvor s t))
)))
