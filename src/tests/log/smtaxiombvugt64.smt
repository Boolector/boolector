(benchmark smtaxiombvugt
 :logic QF_BV
 :extrafuns ((s BitVec[64]))
 :extrafuns ((t BitVec[64]))
 :formula (not (=
    (bvugt s t)  (bvult t s)
)))
