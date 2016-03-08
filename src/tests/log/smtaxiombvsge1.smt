(benchmark smtaxiombvsge
 :logic QF_BV
 :extrafuns ((s BitVec[1]))
 :extrafuns ((t BitVec[1]))
 :formula (not (=
    (bvsge s t)  (bvsle t s)
)))
