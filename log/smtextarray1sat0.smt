(benchmark smtextarray1sat0
  :logic QF_AUFBV
  :extrafuns ((a Array[1:1]))
  :extrafuns ((b Array[1:1]))
  :assumption (= (select a bv1[1]) (select b bv1[1]))
  :formula (not (= a b))
)
