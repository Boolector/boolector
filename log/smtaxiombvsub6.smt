(benchmark smtaxiombvsub
 :logic QF_BV
 :extrafuns ((s BitVec[6]))
 :extrafuns ((t BitVec[6]))
 :formula (not (=
(bvsub s t)  (bvadd s (bvneg t))
)))
