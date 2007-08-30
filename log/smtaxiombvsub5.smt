(benchmark smtaxiombvsub
 :logic QF_BV
 :extrafuns ((s BitVec[5]))
 :extrafuns ((t BitVec[5]))
 :formula (not (=
(bvsub s t)  (bvadd s (bvneg t))
)))
