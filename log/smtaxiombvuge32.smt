(benchmark smtaxiombvuge
 :logic QF_BV
 :extrafuns ((s BitVec[32]))
 :extrafuns ((t BitVec[32]))
 :formula (not (=
    (bvuge s t)  (or (bvult t s) (= s t))
)))
