(benchmark smtaxiombvsub
 :logic QF_BV
 :extrafuns ((s BitVec[16]))
 :extrafuns ((t BitVec[16]))
 :formula (not (=
(bvsub s t)  (bvadd s (bvneg t))
)))
