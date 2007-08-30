(benchmark smtaxiombvsle
 :logic QF_BV
 :extrafuns ((s BitVec[64]))
 :extrafuns ((t BitVec[64]))
 :formula (not (=
    (bvsle s t) 
      (or (and (= (extract[63:63] s) bit1)
               (= (extract[63:63] t) bit0))
          (and (= (extract[63:63] s) (extract[63:63] t))
               (bvule s t)))
)))
