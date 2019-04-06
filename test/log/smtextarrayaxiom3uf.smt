(benchmark smtextarrayaxiom3uf
  :logic QF_AUFBV
  :extrafuns ((a Array[3:3]))
  :extrafuns ((b Array[3:3]))
  :extrafuns ((i BitVec[3]))
  :assumption (= a b)
  :formula (not (= (select a i) (select b i)))
)
