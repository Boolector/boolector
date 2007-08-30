(benchmark smtaxiombvsle
 :logic QF_BV
 :extrafuns ((s BitVec[1]))
 :extrafuns ((t BitVec[1]))
 :formula (not (=
    (bvsle s t) 
      (or (and (= (extract[0:0] s) bit1)
               (= (extract[0:0] t) bit0))
          (and (= (extract[0:0] s) (extract[0:0] t))
               (bvule s t)))
)))
