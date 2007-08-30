(benchmark smtaxiombvsdiv
 :logic QF_BV
 :extrafuns ((s BitVec[2]))
 :extrafuns ((t BitVec[2]))
 :formula (not (=
(bvsdiv s t) 
  (let (?msb_s (extract[1:1] s))
  (let (?msb_t (extract[1:1] t))
  (ite (and (= ?msb_s bit0) (= ?msb_t bit0))
       (bvudiv s t)
  (ite (and (= ?msb_s bit1) (= ?msb_t bit0))
       (bvneg (bvudiv (bvneg s) t))
  (ite (and (= ?msb_s bit0) (= ?msb_t bit1))
       (bvneg (bvudiv s (bvneg t)))
       (bvudiv (bvneg s) (bvneg t)))))))
)))
