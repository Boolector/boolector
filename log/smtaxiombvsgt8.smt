(benchmark smtaxiombvsgt
 :logic QF_BV
 :extrafuns ((s BitVec[8]))
 :extrafuns ((t BitVec[8]))
 :formula (not (=
    (bvsgt s t)  (bvslt t s)
)))
