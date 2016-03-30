(benchmark smtextarrayaxiom1uf
  :logic QF_AUFBV
  :extrafuns ((a Array[1:1]))
  :extrafuns ((b Array[1:1]))
  :extrafuns ((i BitVec[1]))
  :assumption (= a b)
  :formula (not (= (select a i) (select b i)))
)
