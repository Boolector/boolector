(benchmark smtaxiombvsgt
 :logic QF_BV
 :extrafuns ((s BitVec[5]))
 :extrafuns ((t BitVec[5]))
 :formula (not (=
    (bvsgt s t)  (bvslt t s)
)))
