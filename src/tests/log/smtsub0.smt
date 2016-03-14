(benchmark smtsub0
  :logic QF_AUFBV
  :extrafuns ((a BitVec[32]))
  :extrafuns ((b BitVec[32]))
  :assumption (= b (bvnot a))
  :extrafuns ((c BitVec[32]))
  :assumption (= c (bvnot b))
  :extrafuns ((d BitVec[32]))
  :assumption (= d (bvnot c))
  :extrafuns ((e BitVec[32]))
  :assumption (= e (bvnot d))
  :extrafuns ((f BitVec[32]))
  :assumption (= f (bvnot f))
  :formula (= a f))
