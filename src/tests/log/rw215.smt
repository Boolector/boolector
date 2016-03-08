(benchmark fuzzsmt
:logic QF_AUFBV
:extrafuns ((v0 BitVec[1]))
:extrafuns ((v1 BitVec[2]))
:extrafuns ((v2 BitVec[1]))
:status unknown
:formula
(let (?n1 bv0[1])
(let (?n2 (concat v0 ?n1))
(let (?n3 (zero_extend[1] v2))
(let (?n4 (bvand ?n2 ?n3))
(let (?n5 bv0[2])
(flet ($n6 (= ?n4 ?n5))
(flet ($n7 (not $n6))
(let (?n8 (zero_extend[1] v0))
(flet ($n9 (distinct v1 ?n8))
(flet ($n10 (not $n9))
(flet ($n11 (and $n7 $n10))
$n11
))))))))))))
