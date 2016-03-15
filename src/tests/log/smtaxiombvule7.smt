(benchmark smtaxiombvule
 :logic QF_BV
 :extrafuns ((s BitVec[7]))
 :extrafuns ((t BitVec[7]))
 :formula (not (=
(bvule s t)  (or (bvult s t) (= s t))
)))
