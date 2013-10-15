(benchmark fuzzsmt
:logic QF_AUFBV
:extrafuns ((v3 BitVec[4]))
:extrafuns ((v2 BitVec[1]))
:status unknown
:formula
(let (?n1 (zero_extend[3] v2))
(let (?n2 (bvxor v3 ?n1))
(let (?n3 (rotate_left[3] v3))
(let (?n4 (bvlshr ?n2 ?n3))
(let (?n5 bv0[4])
(flet ($n6 (= ?n4 ?n5))
(flet ($n7 (not $n6))
$n7
))))))))
