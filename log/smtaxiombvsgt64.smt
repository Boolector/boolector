(benchmark smtaxiombvsgt
 :logic QF_BV
 :extrafuns ((s BitVec[64]))
 :extrafuns ((t BitVec[64]))
 :formula (not (=
    (bvsgt s t)  (bvslt t s)
)))
