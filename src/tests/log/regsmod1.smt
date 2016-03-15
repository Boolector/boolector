(benchmark fuzzsmt
:logic QF_BV
:status unknown
:formula
(let (?n1 bv0[11])
(let (?n2 bv4[3])
(let (?n3 (sign_extend[8] ?n2))
(let (?n4 (bvsmod ?n1 ?n3))
(flet ($n5 (= ?n1 ?n4))
(flet ($n6 (not $n5))
$n6
)))))))
