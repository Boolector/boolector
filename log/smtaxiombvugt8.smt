(benchmark smtaxiombvugt
 :logic QF_BV
 :extrafuns ((s BitVec[8]))
 :extrafuns ((t BitVec[8]))
 :formula (not (=
    (bvugt s t)  (bvult t s)
)))
