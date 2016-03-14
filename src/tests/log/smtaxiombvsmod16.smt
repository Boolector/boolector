(benchmark smtaxiombvsmod
 :logic QF_BV
 :extrafuns ((s BitVec[16]))
 :extrafuns ((t BitVec[16]))
 :formula (not (=
    (bvsmod s t) 
      (let (?msb_s (extract[15:15] s))
      (let (?msb_t (extract[15:15] t))
      (let (?nrm_s (ite ?msb_s (bvneg s) s))
      (let (?nrm_t (ite ?msb_t (bvneg t) t))
      (let (?nurem (bvurem ?nrm_s ?nrm_t))
      (let (?nuremzero (= ?nurem bv0[16]))
      (ite (and (= ?msb_s bit0) (= ?msb_t bit0))
           ?nurem
      (ite (and (= ?msb_s bit1) (= ?msb_t bit0))
           (ite ?nuremzero bv0[16] (bvadd (bvneg ?nurem) t))
      (ite (and (= ?msb_s bit0) (= ?msb_t bit1))
           (ite ?nuremzero bv0[16] (bvadd ?nurem t))
           (bvneg ?nurem))))))))))
)))
