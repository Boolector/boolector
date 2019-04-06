(benchmark smtarraycond1
  :logic QF_AUFBV
  :extrafuns ((a Array[32:8]))
  :extrafuns ((b Array[32:8]))
  :extrafuns ((i BitVec[32]))
  :extrapreds ((c))
  :formula 
  (not (= (ite c (select a i) (select b i)) (select (ite c a b) i))))

