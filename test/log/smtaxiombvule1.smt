(benchmark smtaxiombvule
 :logic QF_BV
 :extrafuns ((s BitVec[1]))
 :extrafuns ((t BitVec[1]))
 :formula (not (=
(bvule s t)  (or (bvult s t) (= s t))
)))
