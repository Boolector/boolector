(benchmark smtaxiombvsdiv
 :logic QF_BV
 :extrafuns ((s BitVec[1]))
 :extrafuns ((t BitVec[1]))
 :formula (not (=
(bvsdiv s t) 
  (let (?msb_s (extract[0:0] s))
  (let (?msb_t (extract[0:0] t))
  (ite (and (= ?msb_s bit0) (= ?msb_t bit0))
       (bvudiv s t)
  (ite (and (= ?msb_s bit1) (= ?msb_t bit0))
       (bvneg (bvudiv (bvneg s) t))
  (ite (and (= ?msb_s bit0) (= ?msb_t bit1))
       (bvneg (bvudiv s (bvneg t)))
       (bvudiv (bvneg s) (bvneg t)))))))
)))
