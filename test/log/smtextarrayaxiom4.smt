(benchmark smtextarrayaxiom4
  :logic QF_AUFBV
  :extrafuns ((a Array[4:4]))
  :extrafuns ((b Array[4:4]))

  :assumption (= (select a bv0[4]) (select b bv0[4]))
  :assumption (= (select a bv1[4]) (select b bv1[4]))
  :assumption (= (select a bv2[4]) (select b bv2[4]))
  :assumption (= (select a bv3[4]) (select b bv3[4]))

  :assumption (= (select a bv4[4]) (select b bv4[4]))
  :assumption (= (select a bv5[4]) (select b bv5[4]))
  :assumption (= (select a bv6[4]) (select b bv6[4]))
  :assumption (= (select a bv7[4]) (select b bv7[4]))

  :assumption (= (select a bv8[4]) (select b bv8[4]))
  :assumption (= (select a bv9[4]) (select b bv9[4]))
  :assumption (= (select a bv10[4]) (select b bv10[4]))
  :assumption (= (select a bv11[4]) (select b bv11[4]))

  :assumption (= (select a bv12[4]) (select b bv12[4]))
  :assumption (= (select a bv13[4]) (select b bv13[4]))
  :assumption (= (select a bv14[4]) (select b bv14[4]))
  :assumption (= (select a bv15[4]) (select b bv15[4]))

  :formula (not (= a b))
)
