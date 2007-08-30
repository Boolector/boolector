(benchmark smtaxiombvsub
 :logic QF_BV
 :extrafuns ((s BitVec[1]))
 :extrafuns ((t BitVec[1]))
 :formula (not (=
(bvsub s t)  (bvadd s (bvneg t))
)))
