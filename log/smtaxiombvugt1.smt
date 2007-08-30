(benchmark smtaxiombvugt
 :logic QF_BV
 :extrafuns ((s BitVec[1]))
 :extrafuns ((t BitVec[1]))
 :formula (not (=
    (bvugt s t)  (bvult t s)
)))
