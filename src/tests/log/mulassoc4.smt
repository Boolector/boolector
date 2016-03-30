(benchmark mullassoc
 :logic QF_BV
 :extrafuns ((a BitVec[4]))
 :extrafuns ((b BitVec[4]))
 :extrafuns ((c BitVec[4]))
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
