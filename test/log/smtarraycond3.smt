(benchmark smtarraycond3
  :logic QF_AUFBV
  :extrafuns ((a Array[32:8]))
  :extrafuns ((b Array[32:8]))
  :extrafuns ((i BitVec[32]))
  :extrafuns ((j BitVec[32]))
  :extrafuns ((v BitVec[8]))
  :extrapreds ((c))
  :formula 
  (not 
    (=
      (select (ite c (store a i v) (store b i v)) j)
      (select (store (ite c a b) i v) j)))
)
