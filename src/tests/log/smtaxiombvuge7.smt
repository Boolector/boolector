(benchmark smtaxiombvuge
 :logic QF_BV
 :extrafuns ((s BitVec[7]))
 :extrafuns ((t BitVec[7]))
 :formula (not (=
    (bvuge s t)  (or (bvult t s) (= s t))
)))
