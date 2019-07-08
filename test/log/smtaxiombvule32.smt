(benchmark smtaxiombvule
 :logic QF_BV
 :extrafuns ((s BitVec[32]))
 :extrafuns ((t BitVec[32]))
 :formula (not (=
(bvule s t)  (or (bvult s t) (= s t))
)))
