(benchmark bubsort002un.smt
:source {
We verify that bubble sort sorts an array
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
(let (?e11 (bvadd ?e1 start))
(let (?e12 (select a2 start))
(let (?e13 (select a2 ?e11))
(let (?e14 (ite (bvult ?e13 ?e12) bv1[1] bv0[1]))
(let (?e15 (ite (= bv1[1] ?e14) ?e13 ?e12))
(let (?e16 (ite (= bv1[1] ?e14) ?e12 ?e13))
(let (?e17 (store a2 start ?e15))
(let (?e18 (store ?e17 ?e11 ?e16))
(let (?e19 bv1[1])
(let (?e20 (select ?e18 start))
(let (?e21 (ite (bvult ?e16 ?e20) bv1[1] bv0[1]))
(let (?e22 (bvand ?e19 (bvnot ?e21)))
(let (?e23 (ite (= ?e10 ?e20) bv1[1] bv0[1]))
(let (?e24 (bvand ?e19 (bvnot ?e23)))
(let (?e25 (ite (= ?e10 ?e16) bv1[1] bv0[1]))
(let (?e26 (bvand ?e24 (bvnot ?e25)))
(let (?e27 (bvand ?e9 ?e26))
(let (?e28 (bvand ?e22 (bvnot ?e27)))
(not (= (bvnot ?e28) bv0[1]))
))))))))))))))))))))))))))
