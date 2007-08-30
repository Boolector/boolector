(benchmark smtaxiombvslt
 :logic QF_BV
 :extrafuns ((s BitVec[2]))
 :extrafuns ((t BitVec[2]))
 :formula (not (=
    (bvslt s t) 
      (or (and (= (extract[1:1] s) bit1)
               (= (extract[1:1] t) bit0))
          (and (= (extract[1:1] s) (extract[1:1] t))
               (bvult s t)))
)))
