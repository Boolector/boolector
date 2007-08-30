(benchmark smtaxiombvule
 :logic QF_BV
 :extrafuns ((s BitVec[2]))
 :extrafuns ((t BitVec[2]))
 :formula (not (=
(bvule s t)  (or (bvult s t) (= s t))
)))
