(benchmark smtaxiombvslt
 :logic QF_BV
 :extrafuns ((s BitVec[16]))
 :extrafuns ((t BitVec[16]))
 :formula (not (=
    (bvslt s t) 
      (or (and (= (extract[15:15] s) bit1)
               (= (extract[15:15] t) bit0))
          (and (= (extract[15:15] s) (extract[15:15] t))
               (bvult s t)))
)))
