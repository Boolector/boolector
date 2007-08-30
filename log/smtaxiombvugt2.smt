(benchmark smtaxiombvugt
 :logic QF_BV
 :extrafuns ((s BitVec[2]))
 :extrafuns ((t BitVec[2]))
 :formula (not (=
    (bvugt s t)  (bvult t s)
)))
