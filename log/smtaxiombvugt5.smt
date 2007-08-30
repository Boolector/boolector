(benchmark smtaxiombvugt
 :logic QF_BV
 :extrafuns ((s BitVec[5]))
 :extrafuns ((t BitVec[5]))
 :formula (not (=
    (bvugt s t)  (bvult t s)
)))
