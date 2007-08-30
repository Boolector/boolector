(benchmark smtaxiombvule
 :logic QF_BV
 :extrafuns ((s BitVec[64]))
 :extrafuns ((t BitVec[64]))
 :formula (not (=
(bvule s t)  (or (bvult s t) (= s t))
)))
