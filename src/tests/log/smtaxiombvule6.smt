(benchmark smtaxiombvule
 :logic QF_BV
 :extrafuns ((s BitVec[6]))
 :extrafuns ((t BitVec[6]))
 :formula (not (=
(bvule s t)  (or (bvult s t) (= s t))
)))
