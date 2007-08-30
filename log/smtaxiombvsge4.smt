(benchmark smtaxiombvsge
 :logic QF_BV
 :extrafuns ((s BitVec[4]))
 :extrafuns ((t BitVec[4]))
 :formula (not (=
    (bvsge s t)  (bvsle t s)
)))
