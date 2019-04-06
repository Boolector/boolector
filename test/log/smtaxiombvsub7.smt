(benchmark smtaxiombvsub
 :logic QF_BV
 :extrafuns ((s BitVec[7]))
 :extrafuns ((t BitVec[7]))
 :formula (not (=
(bvsub s t)  (bvadd s (bvneg t))
)))
