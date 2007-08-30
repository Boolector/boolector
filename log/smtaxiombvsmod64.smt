(benchmark smtaxiombvsmod
 :logic QF_BV
 :extrafuns ((s BitVec[64]))
 :extrafuns ((t BitVec[64]))
 :formula (not (=
    (bvsmod s t) 
      (let (?msb_s (extract[63:63] s))
      (let (?msb_t (extract[63:63] t))
      (ite (and (= ?msb_s bit0) (= ?msb_t bit0))
           (bvurem s t)
      (ite (and (= ?msb_s bit1) (= ?msb_t bit0))
           (bvadd (bvneg (bvurem (bvneg s) t)) t)
      (ite (and (= ?msb_s bit0) (= ?msb_t bit1))
           (bvadd (bvurem s (bvneg t)) t)
           (bvneg (bvurem (bvneg s) (bvneg t))))))))
)))
