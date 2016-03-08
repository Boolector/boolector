(benchmark smtaxiombvule
 :logic QF_BV
 :extrafuns ((s BitVec[8]))
 :extrafuns ((t BitVec[8]))
 :formula (not (=
(bvule s t)  (or (bvult s t) (= s t))
)))
