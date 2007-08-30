(benchmark smtaxiombvsge
 :logic QF_BV
 :extrafuns ((s BitVec[32]))
 :extrafuns ((t BitVec[32]))
 :formula (not (=
    (bvsge s t)  (bvsle t s)
)))
