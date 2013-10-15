(benchmark root3
:logic QF_AUFBV
:extrafuns ((a1 Array[0:1]))
:formula
(let (?e2 bv0[1])
(let (?e3 (select a1 ?e2))
(not (= ?e3 bv0[1]))
)))
