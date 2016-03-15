(benchmark smtaxiombvugt
 :logic QF_BV
 :extrafuns ((s BitVec[6]))
 :extrafuns ((t BitVec[6]))
 :formula (not (=
    (bvugt s t)  (bvult t s)
)))
