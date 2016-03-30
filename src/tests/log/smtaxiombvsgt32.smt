(benchmark smtaxiombvsgt
 :logic QF_BV
 :extrafuns ((s BitVec[32]))
 :extrafuns ((t BitVec[32]))
 :formula (not (=
    (bvsgt s t)  (bvslt t s)
)))
