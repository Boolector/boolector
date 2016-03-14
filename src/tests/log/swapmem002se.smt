(benchmark swapmem002se.smt
:source {
We swap two byte sequences of length 2 twice in memory.
The sequences can overlap, hence it is not always the case
that swapping them twice yields the initial memory.

Swapping is done via XOR in the following way:
x ^= y;
y ^= x;
x ^= y;

Contributed by Robert Brummayer (robert.brummayer@gmail.com).
}
:status sat
:category { crafted }
:logic QF_AUFBV
:extrafuns ((a1 Array[32:8]))
:extrafuns ((start1 BitVec[32]))
:extrafuns ((start2 BitVec[32]))
:formula
(let (?e4 bv1[32])
(let (?e5 (select a1 start1))
(let (?e6 (select a1 start2))
(let (?e7 (bvand (bvnot ?e5) (bvnot ?e6)))
(let (?e8 (bvand ?e5 ?e6))
(let (?e9 (bvand (bvnot ?e7) (bvnot ?e8)))
(let (?e10 (store a1 start1 ?e9))
(let (?e11 (bvand (bvnot ?e6) (bvnot ?e9)))
(let (?e12 (bvand ?e6 ?e9))
(let (?e13 (bvand (bvnot ?e11) (bvnot ?e12)))
(let (?e14 (store ?e10 start2 ?e13))
(let (?e15 (bvand (bvnot ?e9) (bvnot ?e13)))
(let (?e16 (bvand ?e9 ?e13))
(let (?e17 (bvand (bvnot ?e15) (bvnot ?e16)))
(let (?e18 (store ?e14 start1 ?e17))
(let (?e19 (bvadd start1 ?e4))
(let (?e20 (bvadd start2 ?e4))
(let (?e21 (select ?e18 ?e19))
(let (?e22 (select ?e18 ?e20))
(let (?e23 (bvand (bvnot ?e21) (bvnot ?e22)))
(let (?e24 (bvand ?e21 ?e22))
(let (?e25 (bvand (bvnot ?e23) (bvnot ?e24)))
(let (?e26 (store ?e18 ?e19 ?e25))
(let (?e27 (bvand (bvnot ?e22) (bvnot ?e25)))
(let (?e28 (bvand ?e22 ?e25))
(let (?e29 (bvand (bvnot ?e27) (bvnot ?e28)))
(let (?e30 (store ?e26 ?e20 ?e29))
(let (?e31 (bvand (bvnot ?e25) (bvnot ?e29)))
(let (?e32 (bvand ?e25 ?e29))
(let (?e33 (bvand (bvnot ?e31) (bvnot ?e32)))
(let (?e34 (store ?e30 ?e19 ?e33))
(let (?e35 (select ?e34 start1))
(let (?e36 (select ?e34 start2))
(let (?e37 (bvand (bvnot ?e35) (bvnot ?e36)))
(let (?e38 (bvand ?e35 ?e36))
(let (?e39 (bvand (bvnot ?e37) (bvnot ?e38)))
(let (?e40 (store ?e34 start1 ?e39))
(let (?e41 (bvand (bvnot ?e36) (bvnot ?e39)))
(let (?e42 (bvand ?e36 ?e39))
(let (?e43 (bvand (bvnot ?e41) (bvnot ?e42)))
(let (?e44 (store ?e40 start2 ?e43))
(let (?e45 (bvand (bvnot ?e39) (bvnot ?e43)))
(let (?e46 (bvand ?e39 ?e43))
(let (?e47 (bvand (bvnot ?e45) (bvnot ?e46)))
(let (?e48 (store ?e44 start1 ?e47))
(let (?e49 (select ?e48 ?e19))
(let (?e50 (select ?e48 ?e20))
(let (?e51 (bvand (bvnot ?e49) (bvnot ?e50)))
(let (?e52 (bvand ?e49 ?e50))
(let (?e53 (bvand (bvnot ?e51) (bvnot ?e52)))
(let (?e54 (store ?e48 ?e19 ?e53))
(let (?e55 (bvand (bvnot ?e50) (bvnot ?e53)))
(let (?e56 (bvand ?e50 ?e53))
(let (?e57 (bvand (bvnot ?e55) (bvnot ?e56)))
(let (?e58 (store ?e54 ?e20 ?e57))
(let (?e59 (bvand (bvnot ?e53) (bvnot ?e57)))
(let (?e60 (bvand ?e53 ?e57))
(let (?e61 (bvand (bvnot ?e59) (bvnot ?e60)))
(let (?e62 (store ?e58 ?e19 ?e61))
(let (?e63 (ite (= a1 ?e62) bv1[1] bv0[1]))
(not (= (bvnot ?e63) bv0[1]))
)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
