(benchmark smtextarrayaxiom2uf
  :logic QF_AUFBV
  :extrafuns ((a Array[2:2]))
  :extrafuns ((b Array[2:2]))
  :extrafuns ((i BitVec[2]))
  :assumption (= a b)
  :formula (not (= (select a i) (select b i)))
)
