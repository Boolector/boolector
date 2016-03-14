(benchmark smtaxiombvsub
 :logic QF_BV
 :extrafuns ((s BitVec[2]))
 :extrafuns ((t BitVec[2]))
 :formula (not (=
(bvsub s t)  (bvadd s (bvneg t))
)))
