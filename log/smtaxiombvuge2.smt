(benchmark smtaxiombvuge
 :logic QF_BV
 :extrafuns ((s BitVec[2]))
 :extrafuns ((t BitVec[2]))
 :formula (not (=
    (bvuge s t)  (or (bvult t s) (= s t))
)))
