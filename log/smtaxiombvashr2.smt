(benchmark smtaxiombvashr
 :logic QF_BV
 :extrafuns ((s BitVec[2]))
 :extrafuns ((t BitVec[2]))
 :formula (not (=
    (bvashr s t)  
      (ite (= (extract[1:1] s) bit0)
           (bvlshr s t)
           (bvnot (bvlshr (bvnot s) t)))
)))
