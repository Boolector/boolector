(benchmark smtaxiombvsgt
 :logic QF_BV
 :extrafuns ((s BitVec[2]))
 :extrafuns ((t BitVec[2]))
 :formula (not (=
    (bvsgt s t)  (bvslt t s)
)))
