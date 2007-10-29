(benchmark smtextarray3sat1
  :logic QF_AUFBV
  :extrafuns ((a Array[3:3]))
  :extrafuns ((b Array[3:3]))
  :assumption (= (select a bv0[3]) (select b bv0[3]))
  ;:assumption (= (select a bv1[3]) (select b bv1[3]))
  :assumption (= (select a bv2[3]) (select b bv2[3]))
  :assumption (= (select a bv3[3]) (select b bv3[3]))
  :assumption (= (select a bv4[3]) (select b bv4[3]))
  :assumption (= (select a bv5[3]) (select b bv5[3]))
  :assumption (= (select a bv6[3]) (select b bv6[3]))
  :assumption (= (select a bv7[3]) (select b bv7[3]))
  :formula (not (= a b))
)
