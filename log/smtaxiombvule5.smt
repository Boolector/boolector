(benchmark smtaxiombvule
 :logic QF_BV
 :extrafuns ((s BitVec[5]))
 :extrafuns ((t BitVec[5]))
 :formula (not (=
(bvule s t)  (or (bvult s t) (= s t))
)))
