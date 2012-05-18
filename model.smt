(benchmark xufv
:logic QF_AUFBV ; SMT1
:extrafuns((A1 Array[32:8]))
:extrafuns((A0 Array[32:8]))
:extrafuns((A2 Array[32:8]))
:extrafuns((res BitVec[8]))
:assumption (= A1 (store A0 bv0[32] (bvadd bv1[8] (select A0 bv0[32]))))
:assumption (= A2 (store A1 bv1[32]  (bvadd bv1[8] (select A1 bv0[32]))))
:assumption (= res  (bvadd (select A2 bv0[32]) (select A2 bv1[32])))
:formula (= res bv13[8])
)
