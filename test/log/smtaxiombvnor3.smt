(benchmark smtaxiombvnor
 :logic QF_BV
 :extrafuns ((s BitVec[3]))
 :extrafuns ((t BitVec[3]))
 :formula (not (=
    (bvnor s t)  (bvnot (bvor s t))
)))
