(benchmark smtaxiombvugt
 :logic QF_BV
 :extrafuns ((s BitVec[16]))
 :extrafuns ((t BitVec[16]))
 :formula (not (=
    (bvugt s t)  (bvult t s)
)))
