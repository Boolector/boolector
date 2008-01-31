(benchmark selsort002un.smt
:source {
We verify that selection sort sorts an array
of length 2 in memory. Additionally, we read an element
at an arbitrary index of the initial array and show that this
element can not be unequal to an element in the sorted array.

Contributed by Robert Brummayer (robert.brummayer@gmail.com).
}
:status unsat
:category { crafted }
:logic QF_AUFBV
:extrafuns ((a2 Array[32:8]))
:extrafuns ((start BitVec[32]))
:extrafuns ((index BitVec[32]))
:formula
(let (?e1 bv1[32])
(let (?e4 bv2[32])
(let (?e5 (bvadd start ?e4))
(let (?e7 (ite (bvult index start) bv1[1] bv0[1]))
(let (?e8 (ite (bvult index ?e5) bv1[1] bv0[1]))
(let (?e9 (bvand (bvnot ?e7) ?e8))
(let (?e10 (select a2 index))
(let (?e11 (select a2 start))
(let (?e12 (bvadd ?e1 start))
(let (?e13 (select a2 ?e12))
(let (?e14 (ite (bvult ?e13 ?e11) bv1[1] bv0[1]))
(let (?e15 (ite (= bv1[1] ?e14) ?e12 start))
(let (?e16 (select a2 ?e15))
(let (?e17 (store a2 start ?e16))
(let (?e18 (store ?e17 ?e15 ?e11))
(let (?e19 bv1[1])
(let (?e20 (select ?e18 start))
(let (?e21 (select ?e18 ?e12))
(let (?e22 (ite (bvult ?e21 ?e20) bv1[1] bv0[1]))
(let (?e23 (bvand ?e19 (bvnot ?e22)))
(let (?e24 (ite (= ?e10 ?e20) bv1[1] bv0[1]))
(let (?e25 (bvand ?e19 (bvnot ?e24)))
(let (?e26 (ite (= ?e10 ?e21) bv1[1] bv0[1]))
(let (?e27 (bvand ?e25 (bvnot ?e26)))
(let (?e28 (bvand ?e9 ?e27))
(let (?e29 (bvand ?e23 (bvnot ?e28)))
(not (= (bvnot ?e29) bv0[1]))
)))))))))))))))))))))))))))
