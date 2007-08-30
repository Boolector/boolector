(benchmark smtaxiombvuge
 :logic QF_BV
 :extrafuns ((s BitVec[5]))
 :extrafuns ((t BitVec[5]))
 :formula (not (=
    (bvuge s t)  (or (bvult t s) (= s t))
)))
