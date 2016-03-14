(benchmark dubreva002ue.smt
:source {
We reverse an array of length 2 twice in memory at 2 positions.
We show via extensionality that memory has to be equal.

In one case swapping elements is done via XOR in the following way:
x ^= y;
y ^= x;
x ^= y;
In the other case the elements are just swapped.

Contributed by Robert Brummayer (robert.brummayer@gmail.com).
}
:status unsat
:category { crafted }
:logic QF_AUFBV
:extrafuns ((a1 Array[32:8]))
:extrafuns ((start1 BitVec[32]))
:extrafuns ((start2 BitVec[32]))
:formula
(let (?e3 bv1[32])
(let (?e4 (bvadd start1 ?e3))
(let (?e5 (select a1 start1))
(let (?e6 (select a1 ?e4))
(let (?e7 (store a1 ?e4 ?e5))
(let (?e8 (store ?e7 start1 ?e6))
(let (?e9 (bvand (bvnot ?e5) (bvnot ?e6)))
(let (?e10 (bvand ?e5 ?e6))
(let (?e11 (bvand (bvnot ?e9) (bvnot ?e10)))
(let (?e12 (store a1 start1 ?e11))
(let (?e13 (bvand (bvnot ?e6) (bvnot ?e11)))
(let (?e14 (bvand ?e6 ?e11))
(let (?e15 (bvand (bvnot ?e13) (bvnot ?e14)))
(let (?e16 (store ?e12 ?e4 ?e15))
(let (?e17 (bvand (bvnot ?e11) (bvnot ?e15)))
(let (?e18 (bvand ?e11 ?e15))
(let (?e19 (bvand (bvnot ?e17) (bvnot ?e18)))
(let (?e20 (store ?e16 start1 ?e19))
(let (?e22 (bvadd ?e3 start2))
(let (?e23 (select ?e8 start2))
(let (?e24 (select ?e8 ?e22))
(let (?e25 (store ?e8 ?e22 ?e23))
(let (?e26 (store ?e25 start2 ?e24))
(let (?e27 (select ?e20 start2))
(let (?e28 (select ?e20 ?e22))
(let (?e29 (bvand (bvnot ?e27) (bvnot ?e28)))
(let (?e30 (bvand ?e27 ?e28))
(let (?e31 (bvand (bvnot ?e29) (bvnot ?e30)))
(let (?e32 (store ?e20 start2 ?e31))
(let (?e33 (bvand (bvnot ?e28) (bvnot ?e31)))
(let (?e34 (bvand ?e28 ?e31))
(let (?e35 (bvand (bvnot ?e33) (bvnot ?e34)))
(let (?e36 (store ?e32 ?e22 ?e35))
(let (?e37 (bvand (bvnot ?e31) (bvnot ?e35)))
(let (?e38 (bvand ?e31 ?e35))
(let (?e39 (bvand (bvnot ?e37) (bvnot ?e38)))
(let (?e40 (store ?e36 start2 ?e39))
(let (?e41 (ite (= ?e26 ?e40) bv1[1] bv0[1]))
(not (= (bvnot ?e41) bv0[1]))
)))))))))))))))))))))))))))))))))))))))
