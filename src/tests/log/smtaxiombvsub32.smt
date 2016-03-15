(benchmark smtaxiombvsub
 :logic QF_BV
 :extrafuns ((s BitVec[32]))
 :extrafuns ((t BitVec[32]))
 :formula (not (=
(bvsub s t)  (bvadd s (bvneg t))
)))
