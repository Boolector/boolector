(benchmark smtaxiombvuge
 :logic QF_BV
 :extrafuns ((s BitVec[16]))
 :extrafuns ((t BitVec[16]))
 :formula (not (=
    (bvuge s t)  (or (bvult t s) (= s t))
)))
