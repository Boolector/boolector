(benchmark smtaxiombvule
 :logic QF_BV
 :extrafuns ((s BitVec[4]))
 :extrafuns ((t BitVec[4]))
 :formula (not (=
(bvule s t)  (or (bvult s t) (= s t))
)))
