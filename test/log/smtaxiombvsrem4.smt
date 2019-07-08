(benchmark smtaxiombvsrem
 :logic QF_BV
 :extrafuns ((s BitVec[4]))
 :extrafuns ((t BitVec[4]))
 :formula (not (=
    (bvsrem s t) 
      (let (?msb_s (extract[3:3] s))
      (let (?msb_t (extract[3:3] t))
      (ite (and (= ?msb_s bit0) (= ?msb_t bit0))
           (bvurem s t)
      (ite (and (= ?msb_s bit1) (= ?msb_t bit0))
           (bvneg (bvurem (bvneg s) t))
      (ite (and (= ?msb_s bit0) (= ?msb_t bit1))
           (bvurem s (bvneg t))
           (bvneg (bvurem (bvneg s) (bvneg t))))))))
)))
