(benchmark smtaxiombvnor
 :logic QF_BV
 :extrafuns ((s BitVec[4]))
 :extrafuns ((t BitVec[4]))
 :formula (not (=
    (bvnor s t)  (bvnot (bvor s t))
)))
