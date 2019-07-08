(benchmark smtaxiombvsub
 :logic QF_BV
 :extrafuns ((s BitVec[8]))
 :extrafuns ((t BitVec[8]))
 :formula (not (=
(bvsub s t)  (bvadd s (bvneg t))
)))
