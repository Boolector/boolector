(benchmark smtaxiombvnor
 :logic QF_BV
 :extrafuns ((s BitVec[1]))
 :extrafuns ((t BitVec[1]))
 :formula (not (=
    (bvnor s t)  (bvnot (bvor s t))
)))
