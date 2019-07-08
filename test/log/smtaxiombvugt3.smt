(benchmark smtaxiombvugt
 :logic QF_BV
 :extrafuns ((s BitVec[3]))
 :extrafuns ((t BitVec[3]))
 :formula (not (=
    (bvugt s t)  (bvult t s)
)))
