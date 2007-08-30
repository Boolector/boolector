(benchmark smtaxiombvsgt
 :logic QF_BV
 :extrafuns ((s BitVec[1]))
 :extrafuns ((t BitVec[1]))
 :formula (not (=
    (bvsgt s t)  (bvslt t s)
)))
