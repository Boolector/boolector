(benchmark smtaxiombvuge
 :logic QF_BV
 :extrafuns ((s BitVec[4]))
 :extrafuns ((t BitVec[4]))
 :formula (not (=
    (bvuge s t)  (or (bvult t s) (= s t))
)))
