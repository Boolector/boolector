(benchmark smtaxiombvslt
 :logic QF_BV
 :extrafuns ((s BitVec[6]))
 :extrafuns ((t BitVec[6]))
 :formula (not (=
    (bvslt s t) 
      (or (and (= (extract[5:5] s) bit1)
               (= (extract[5:5] t) bit0))
          (and (= (extract[5:5] s) (extract[5:5] t))
               (bvult s t)))
)))
