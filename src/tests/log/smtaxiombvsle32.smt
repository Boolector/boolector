(benchmark smtaxiombvsle
 :logic QF_BV
 :extrafuns ((s BitVec[32]))
 :extrafuns ((t BitVec[32]))
 :formula (not (=
    (bvsle s t) 
      (or (and (= (extract[31:31] s) bit1)
               (= (extract[31:31] t) bit0))
          (and (= (extract[31:31] s) (extract[31:31] t))
               (bvule s t)))
)))
