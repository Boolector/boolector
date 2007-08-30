(benchmark smtaxiombvuge
 :logic QF_BV
 :extrafuns ((s BitVec[8]))
 :extrafuns ((t BitVec[8]))
 :formula (not (=
    (bvuge s t)  (or (bvult t s) (= s t))
)))
