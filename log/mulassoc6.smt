(benchmark mullassoc
 :logic QF_BV
 :extrafuns ((a BitVec[6]))
 :extrafuns ((b BitVec[6]))
 :extrafuns ((c BitVec[6]))
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
