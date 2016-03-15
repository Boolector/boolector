(benchmark smtaxiombvsgt
 :logic QF_BV
 :extrafuns ((s BitVec[7]))
 :extrafuns ((t BitVec[7]))
 :formula (not (=
    (bvsgt s t)  (bvslt t s)
)))
