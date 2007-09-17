(benchmark mullassoc
 :logic QF_BV
 :extrafuns ((a BitVec[5]))
 :extrafuns ((b BitVec[5]))
 :extrafuns ((c BitVec[5]))
 :formula 
 (not
  (=
   (bvmul
    a
    (bvmul
     b
     c))
   (bvmul
    (bvmul
     a
     b)
    c))))
