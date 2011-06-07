(benchmark smtaxiombvsmod
 :logic QF_BV
 :extrafuns ((s BitVec[1]))
 :extrafuns ((t BitVec[1]))
 :formula (not (=
    (bvsmod s t) 
      (ite (= s bv0[1]) bv0[1]
      (let (?msb_s (extract[0:0] s))
      (let (?msb_t (extract[0:0] t))
      (ite (and (= ?msb_s bit0) (= ?msb_t bit0))
           (bvurem s t)
      (ite (and (= ?msb_s bit1) (= ?msb_t bit0))
           (bvadd (bvneg (bvurem (bvneg s) t)) t)
      (ite (and (= ?msb_s bit0) (= ?msb_t bit1))
           (bvadd (bvurem s (bvneg t)) t)
           (bvneg (bvurem (bvneg s) (bvneg t)))))))))
)))
