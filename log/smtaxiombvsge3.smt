(benchmark smtaxiombvsge
 :logic QF_BV
 :extrafuns ((s BitVec[3]))
 :extrafuns ((t BitVec[3]))
 :formula (not (=
    (bvsge s t)  (bvsle t s)
)))
