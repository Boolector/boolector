(benchmark root3
:logic QF_AUFBV
:extrafuns ((a1 Array[1:0]))
:formula
(let (?e2 bv0[1])
(let (?e3 (select a1 ?e2))
(not (= ?e3 bv0[1]))
)))
