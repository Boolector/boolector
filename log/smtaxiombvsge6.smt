(benchmark smtaxiombvsge
 :logic QF_BV
 :extrafuns ((s BitVec[6]))
 :extrafuns ((t BitVec[6]))
 :formula (not (=
    (bvsge s t)  (bvsle t s)
)))
