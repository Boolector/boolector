(benchmark smtaxiombvsgt
 :logic QF_BV
 :extrafuns ((s BitVec[6]))
 :extrafuns ((t BitVec[6]))
 :formula (not (=
    (bvsgt s t)  (bvslt t s)
)))
