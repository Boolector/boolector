(benchmark smtaxiombvuge
 :logic QF_BV
 :extrafuns ((s BitVec[6]))
 :extrafuns ((t BitVec[6]))
 :formula (not (=
    (bvuge s t)  (or (bvult t s) (= s t))
)))
