(benchmark smtaxiombvslt
 :logic QF_BV
 :extrafuns ((s BitVec[5]))
 :extrafuns ((t BitVec[5]))
 :formula (not (=
    (bvslt s t) 
      (or (and (= (extract[4:4] s) bit1)
               (= (extract[4:4] t) bit0))
          (and (= (extract[4:4] s) (extract[4:4] t))
               (bvult s t)))
)))
