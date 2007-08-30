(benchmark smtaxiombvuge
 :logic QF_BV
 :extrafuns ((s BitVec[1]))
 :extrafuns ((t BitVec[1]))
 :formula (not (=
    (bvuge s t)  (or (bvult t s) (= s t))
)))
