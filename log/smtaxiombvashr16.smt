(benchmark smtaxiombvashr
 :logic QF_BV
 :extrafuns ((s BitVec[16]))
 :extrafuns ((t BitVec[16]))
 :formula (not (=
    (bvashr s t)  
      (ite (= (extract[15:15] s) bit0)
           (bvlshr s t)
           (bvnot (bvlshr (bvnot s) t)))
)))
