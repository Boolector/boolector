(benchmark smtaxiombvuge
 :logic QF_BV
 :extrafuns ((s BitVec[3]))
 :extrafuns ((t BitVec[3]))
 :formula (not (=
    (bvuge s t)  (or (bvult t s) (= s t))
)))
