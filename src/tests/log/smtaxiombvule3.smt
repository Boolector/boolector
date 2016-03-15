(benchmark smtaxiombvule
 :logic QF_BV
 :extrafuns ((s BitVec[3]))
 :extrafuns ((t BitVec[3]))
 :formula (not (=
(bvule s t)  (or (bvult s t) (= s t))
)))
