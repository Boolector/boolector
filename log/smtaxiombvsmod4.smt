(benchmark smtaxiombvsmod
 :logic QF_BV
 :extrafuns ((s BitVec[4]))
 :extrafuns ((t BitVec[4]))
 :formula (not (=
    (bvsmod s t) 
      (let (?msb_s (extract[3:3] s))
      (let (?msb_t (extract[3:3] t))
      (ite (and (= ?msb_s bit0) (= ?msb_t bit0))
           (bvurem s t)
      (ite (and (= ?msb_s bit1) (= ?msb_t bit0))
           (bvadd (bvneg (bvurem (bvneg s) t)) t)
      (ite (and (= ?msb_s bit0) (= ?msb_t bit1))
           (bvadd (bvurem s (bvneg t)) t)
           (bvneg (bvurem (bvneg s) (bvneg t))))))))
)))
