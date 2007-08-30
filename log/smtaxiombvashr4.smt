(benchmark smtaxiombvashr
 :logic QF_BV
 :extrafuns ((s BitVec[4]))
 :extrafuns ((t BitVec[4]))
 :formula (not (=
    (bvashr s t)  
      (ite (= (extract[3:3] s) bit0)
           (bvlshr s t)
           (bvnot (bvlshr (bvnot s) t)))
)))
