(benchmark smtaxiombvsgt
 :logic QF_BV
 :extrafuns ((s BitVec[4]))
 :extrafuns ((t BitVec[4]))
 :formula (not (=
    (bvsgt s t)  (bvslt t s)
)))
