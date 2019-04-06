(benchmark smtaxiombvugt
 :logic QF_BV
 :extrafuns ((s BitVec[4]))
 :extrafuns ((t BitVec[4]))
 :formula (not (=
    (bvugt s t)  (bvult t s)
)))
