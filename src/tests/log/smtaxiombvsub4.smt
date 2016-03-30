(benchmark smtaxiombvsub
 :logic QF_BV
 :extrafuns ((s BitVec[4]))
 :extrafuns ((t BitVec[4]))
 :formula (not (=
(bvsub s t)  (bvadd s (bvneg t))
)))
