(benchmark smtextarray2sat2
  :logic QF_AUFBV
  :extrafuns ((a Array[2:2]))
  :extrafuns ((b Array[2:2]))
  :assumption (= (select a bv0[2]) (select b bv0[2]))
  :assumption (= (select a bv1[2]) (select b bv1[2]))
  ;:assumption (= (select a bv2[2]) (select b bv2[2]))
  :assumption (= (select a bv3[2]) (select b bv3[2]))
  :formula (not (= a b))
)
