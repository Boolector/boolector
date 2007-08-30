(benchmark smtaxiombvsgt
 :logic QF_BV
 :extrafuns ((s BitVec[16]))
 :extrafuns ((t BitVec[16]))
 :formula (not (=
    (bvsgt s t)  (bvslt t s)
)))
