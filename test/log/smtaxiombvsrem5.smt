(benchmark smtaxiombvsrem
 :logic QF_BV
 :extrafuns ((s BitVec[5]))
 :extrafuns ((t BitVec[5]))
 :formula (not (=
    (bvsrem s t) 
      (let (?msb_s (extract[4:4] s))
      (let (?msb_t (extract[4:4] t))
      (ite (and (= ?msb_s bit0) (= ?msb_t bit0))
           (bvurem s t)
      (ite (and (= ?msb_s bit1) (= ?msb_t bit0))
           (bvneg (bvurem (bvneg s) t))
      (ite (and (= ?msb_s bit0) (= ?msb_t bit1))
           (bvurem s (bvneg t))
           (bvneg (bvurem (bvneg s) (bvneg t))))))))
)))
