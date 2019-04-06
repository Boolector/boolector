(benchmark smtaxiombvnor
 :logic QF_BV
 :extrafuns ((s BitVec[16]))
 :extrafuns ((t BitVec[16]))
 :formula (not (=
    (bvnor s t)  (bvnot (bvor s t))
)))
