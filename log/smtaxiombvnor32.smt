(benchmark smtaxiombvnor
 :logic QF_BV
 :extrafuns ((s BitVec[32]))
 :extrafuns ((t BitVec[32]))
 :formula (not (=
    (bvnor s t)  (bvnot (bvor s t))
)))
