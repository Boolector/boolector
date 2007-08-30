(benchmark smtaxiombvugt
 :logic QF_BV
 :extrafuns ((s BitVec[7]))
 :extrafuns ((t BitVec[7]))
 :formula (not (=
    (bvugt s t)  (bvult t s)
)))
