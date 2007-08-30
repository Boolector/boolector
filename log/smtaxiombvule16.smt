(benchmark smtaxiombvule
 :logic QF_BV
 :extrafuns ((s BitVec[16]))
 :extrafuns ((t BitVec[16]))
 :formula (not (=
(bvule s t)  (or (bvult s t) (= s t))
)))
