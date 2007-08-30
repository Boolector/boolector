(benchmark smtaxiombvsub
 :logic QF_BV
 :extrafuns ((s BitVec[3]))
 :extrafuns ((t BitVec[3]))
 :formula (not (=
(bvsub s t)  (bvadd s (bvneg t))
)))
