(benchmark smtaxiombvsge
 :logic QF_BV
 :extrafuns ((s BitVec[2]))
 :extrafuns ((t BitVec[2]))
 :formula (not (=
    (bvsge s t)  (bvsle t s)
)))
