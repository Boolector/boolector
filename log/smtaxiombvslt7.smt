(benchmark smtaxiombvslt
 :logic QF_BV
 :extrafuns ((s BitVec[7]))
 :extrafuns ((t BitVec[7]))
 :formula (not (=
    (bvslt s t) 
      (or (and (= (extract[6:6] s) bit1)
               (= (extract[6:6] t) bit0))
          (and (= (extract[6:6] s) (extract[6:6] t))
               (bvult s t)))
)))
