(benchmark udivzero
 :logic QF_BV
 :extrafuns ((s BitVec[32]))
 :formula (not (= (bvudiv s bv0[32]) (bvnot bv0[32]))))
