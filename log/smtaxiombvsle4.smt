(benchmark smtaxiombvsle
 :logic QF_BV
 :extrafuns ((s BitVec[4]))
 :extrafuns ((t BitVec[4]))
 :formula (not (=
    (bvsle s t) 
      (or (and (= (extract[3:3] s) bit1)
               (= (extract[3:3] t) bit0))
          (and (= (extract[3:3] s) (extract[3:3] t))
               (bvule s t)))
)))
