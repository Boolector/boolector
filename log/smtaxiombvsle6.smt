(benchmark smtaxiombvsle
 :logic QF_BV
 :extrafuns ((s BitVec[6]))
 :extrafuns ((t BitVec[6]))
 :formula (not (=
    (bvsle s t) 
      (or (and (= (extract[5:5] s) bit1)
               (= (extract[5:5] t) bit0))
          (and (= (extract[5:5] s) (extract[5:5] t))
               (bvule s t)))
)))
