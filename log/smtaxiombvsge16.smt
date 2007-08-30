(benchmark smtaxiombvsge
 :logic QF_BV
 :extrafuns ((s BitVec[16]))
 :extrafuns ((t BitVec[16]))
 :formula (not (=
    (bvsge s t)  (bvsle t s)
)))
