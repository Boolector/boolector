(benchmark smtaxiombvugt
 :logic QF_BV
 :extrafuns ((s BitVec[32]))
 :extrafuns ((t BitVec[32]))
 :formula (not (=
    (bvugt s t)  (bvult t s)
)))
