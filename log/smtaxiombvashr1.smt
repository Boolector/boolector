(benchmark smtaxiombvashr
 :logic QF_BV
 :extrafuns ((s BitVec[1]))
 :extrafuns ((t BitVec[1]))
 :formula (not (=
    (bvashr s t)  
      (ite (= (extract[0:0] s) bit0)
           (bvlshr s t)
           (bvnot (bvlshr (bvnot s) t)))
)))
