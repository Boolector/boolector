(benchmark smtaxiombvsle
 :logic QF_BV
 :extrafuns ((s BitVec[3]))
 :extrafuns ((t BitVec[3]))
 :formula (not (=
    (bvsle s t) 
      (or (and (= (extract[2:2] s) bit1)
               (= (extract[2:2] t) bit0))
          (and (= (extract[2:2] s) (extract[2:2] t))
               (bvule s t)))
)))
