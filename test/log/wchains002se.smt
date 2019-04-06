(benchmark wchains002se.smt
:source {
This benchmark generates write chain permutations and tries to show
via extensionality that they are equal.

Contributed by Armin Biere (armin.biere@jku.at).
}
:status sat
:category { crafted }
:logic QF_AUFBV
:extrafuns ((a1 Array[32:8]))
:extrafuns ((v6 BitVec[32]))
:extrafuns ((v7 BitVec[32]))
:formula
(let (?e2 bv0[32])
(let (?e3 bv1[32])
(let (?e4 bv2[32])
(let (?e5 bv3[32])
(let (?e8 (bvadd ?e2 v6))
(let (?e9 (extract[7:0] v6))
(let (?e10 (store a1 ?e8 ?e9))
(let (?e11 (bvadd ?e3 v6))
(let (?e12 (extract[15:8] v6))
(let (?e13 (store ?e10 ?e11 ?e12))
(let (?e14 (bvadd ?e4 v6))
(let (?e15 (extract[23:16] v6))
(let (?e16 (store ?e13 ?e14 ?e15))
(let (?e17 (bvadd ?e5 v6))
(let (?e18 (extract[31:24] v6))
(let (?e19 (store ?e16 ?e17 ?e18))
(let (?e20 (bvadd ?e2 v7))
(let (?e21 (extract[7:0] v7))
(let (?e22 (store ?e19 ?e20 ?e21))
(let (?e23 (bvadd ?e3 v7))
(let (?e24 (extract[15:8] v7))
(let (?e25 (store ?e22 ?e23 ?e24))
(let (?e26 (bvadd ?e4 v7))
(let (?e27 (extract[23:16] v7))
(let (?e28 (store ?e25 ?e26 ?e27))
(let (?e29 (bvadd ?e5 v7))
(let (?e30 (extract[31:24] v7))
(let (?e31 (store ?e28 ?e29 ?e30))
(let (?e32 (store a1 ?e20 ?e21))
(let (?e33 (store ?e32 ?e23 ?e24))
(let (?e34 (store ?e33 ?e26 ?e27))
(let (?e35 (store ?e34 ?e29 ?e30))
(let (?e36 (store ?e35 ?e8 ?e9))
(let (?e37 (store ?e36 ?e11 ?e12))
(let (?e38 (store ?e37 ?e14 ?e15))
(let (?e39 (store ?e38 ?e17 ?e18))
(let (?e40 (ite (= ?e31 ?e39) bv1[1] bv0[1]))
(not (= (bvnot ?e40) bv0[1]))
))))))))))))))))))))))))))))))))))))))
