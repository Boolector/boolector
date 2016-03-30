(benchmark smtaxiombvsgt
 :logic QF_BV
 :extrafuns ((s BitVec[3]))
 :extrafuns ((t BitVec[3]))
 :formula (not (=
    (bvsgt s t)  (bvslt t s)
)))
