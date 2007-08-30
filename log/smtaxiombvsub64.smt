(benchmark smtaxiombvsub
 :logic QF_BV
 :extrafuns ((s BitVec[64]))
 :extrafuns ((t BitVec[64]))
 :formula (not (=
(bvsub s t)  (bvadd s (bvneg t))
)))
