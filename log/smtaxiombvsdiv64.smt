(benchmark smtaxiombvsdiv
 :logic QF_BV
 :extrafuns ((s BitVec[64]))
 :extrafuns ((t BitVec[64]))
 :formula (not (=
(bvsdiv s t) 
  (let (?msb_s (extract[63:63] s))
  (let (?msb_t (extract[63:63] t))
  (ite (and (= ?msb_s bit0) (= ?msb_t bit0))
       (bvudiv s t)
  (ite (and (= ?msb_s bit1) (= ?msb_t bit0))
       (bvneg (bvudiv (bvneg s) t))
  (ite (and (= ?msb_s bit0) (= ?msb_t bit1))
       (bvneg (bvudiv s (bvneg t)))
       (bvudiv (bvneg s) (bvneg t)))))))
)))
