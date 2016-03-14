(benchmark memcpy02.smt
:source {
We verify the correctness of the memcpy algorithm.
We represent main memory as byte array of size 2 ^ 32,
and model the memcpy algorithm with pointer arithmetic.
We assume that the memory locations do not overlap.
Length: 2

Contributed by Armin Biere (armin.biere@jku.at).
}
:status unsat
:category { crafted }
:logic QF_AUFBV
:extrafuns ((a1 Array[32:8]))
:extrafuns ((src BitVec[32]))
:extrafuns ((dst BitVec[32]))
:extrafuns ((j BitVec[32]))
:formula
(let (?e4 bv2[32])
(let (?e6 bv1[32])
(let (?e7 (bvadd src ?e4))
(let (?e8 (bvadd dst ?e4))
(let (?e9 (ite (bvult ?e7 src) bv1[1] bv0[1]))
(let (?e10 (ite (bvult ?e8 dst) bv1[1] bv0[1]))
(let (?e11 (bvand (bvnot ?e9) (bvnot ?e10)))
(let (?e12 (ite (bvult dst ?e7) bv1[1] bv0[1]))
(let (?e13 (ite (bvult src ?e8) bv1[1] bv0[1]))
(let (?e14 (bvand ?e12 ?e13))
(let (?e15 (bvand ?e11 (bvnot ?e14)))
(let (?e16 (ite (bvult j ?e4) bv1[1] bv0[1]))
(let (?e17 (bvand ?e15 ?e16))
(let (?e18 (bvadd src j))
(let (?e19 (select a1 ?e18))
(let (?e20 (select a1 src))
(let (?e21 (store a1 dst ?e20))
(let (?e22 (bvadd src ?e6))
(let (?e23 (bvadd dst ?e6))
(let (?e24 (select ?e21 ?e22))
(let (?e25 (store ?e21 ?e23 ?e24))
(let (?e26 (bvadd dst j))
(let (?e27 (select ?e25 ?e26))
(let (?e28 (ite (= ?e19 ?e27) bv1[1] bv0[1]))
(let (?e29 (bvand ?e17 (bvnot ?e28)))
(not (= ?e29 bv0[1]))
))))))))))))))))))))))))))
