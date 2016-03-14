(benchmark smtextarray1sat1
  :logic QF_AUFBV
  :extrafuns ((a Array[1:1]))
  :extrafuns ((b Array[1:1]))
  :assumption (= (select a bv0[1]) (select b bv0[1]))
  :formula (not (= a b))
)
