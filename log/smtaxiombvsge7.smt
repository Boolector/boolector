(benchmark smtaxiombvsge
 :logic QF_BV
 :extrafuns ((s BitVec[7]))
 :extrafuns ((t BitVec[7]))
 :formula (not (=
    (bvsge s t)  (bvsle t s)
)))
