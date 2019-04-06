(benchmark fuzzsmt
:logic QF_AUFBV
:extrafuns ((v1 BitVec[2]))
:extrafuns ((v0 BitVec[1]))
:status unknown
:formula
(let (?n1 (zero_extend[3] v0))
(let (?n2 bv0[1])
(let (?n3 (concat v1 ?n2))
(let (?n4 (sign_extend[1] ?n3))
(let (?n5 (bvand ?n1 ?n4))
(let (?n6 bv0[4])
(flet ($n7 (= ?n5 ?n6))
(flet ($n8 (not $n7))
$n8
)))))))))
