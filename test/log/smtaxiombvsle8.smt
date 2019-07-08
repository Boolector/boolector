(benchmark smtaxiombvsle
 :logic QF_BV
 :extrafuns ((s BitVec[8]))
 :extrafuns ((t BitVec[8]))
 :formula (not (=
    (bvsle s t) 
      (or (and (= (extract[7:7] s) bit1)
               (= (extract[7:7] t) bit0))
          (and (= (extract[7:7] s) (extract[7:7] t))
               (bvule s t)))
)))
