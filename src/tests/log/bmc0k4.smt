(benchmark bmc
:source {
  Armin Biere, FMV, JKU, June, 2011.

  Incremental example, assumptions are added eagerly.

  Formulas are only checked individually and not asserted permanently
  Start with all bits zero state.

  The input vectors i0, i1, ... have the same size as the state s0, s1, ...
  vectors and are simply added to them to get the next state.

  Toggle at most one bit per step using the Hacker Delight trick
  '(i & (i-1)) == 0' iff i has exactly one bit set.
}
:logic QF_BV
;------------------------------------ bad
:extrafuns ((goal BitVec[4]))
:assumption (= goal bv15[4])
;------------------------------------ global constant
:extrafuns ((zero BitVec[4]))
:extrafuns ((one BitVec[4]))
:assumption (= zero bv0[4])
:assumption (= one bv1[4])
;------------------------------------ s0
:extrafuns ((s0 BitVec[4]))
:assumption (= s0 zero) ; INIT
:formula (= s0 goal)
;------------------------------------ s1
:extrafuns ((i0 BitVec[4])); input i0 (global)
:assumption ; INVAR: force i0 to have at most one bit set
(let (?d (bvsub i0 one)) ; dec = unshared among time frames
(let (?a (bvand i0 ?d)) ; and = unshared among time frames
(= ?a zero)))
:extrafuns ((s1 BitVec[4])); state i1 (global)
:assumption ; TRANS: add i0 to s0 to get s1
(let (?n (bvadd s0 i0)) ; next = unshared among time frames
(= s1 ?n))
:formula (= s1 goal)
;------------------------------------ s2
;
; shorter version without redundant lets
;
:extrafuns ((i1 BitVec[4]))
:extrafuns ((s2 BitVec[4]));
:assumption (= (bvand i1 (bvsub i1 one)) zero)
:assumption (= s2 (bvadd s1 i1))
:formula (= s2 goal)
;------------------------------------ s3
:extrafuns ((i2 BitVec[4]))
:extrafuns ((s3 BitVec[4]));
:assumption (= (bvand i2 (bvsub i2 one)) zero)
:assumption (= s3 (bvadd s2 i2))
:formula (= s3 goal)
;------------------------------------ s4
:extrafuns ((i3 BitVec[4]))
:extrafuns ((s4 BitVec[4]));
:assumption (= (bvand i3 (bvsub i3 one)) zero)
:assumption (= s4 (bvadd s3 i3))
:formula (= s4 goal)
;------------------------------------ s5
:extrafuns ((i4 BitVec[4]))
:extrafuns ((s5 BitVec[4]));
:assumption (= (bvand i4 (bvsub i4 one)) zero)
:assumption (= s5 (bvadd s4 i4))
:formula (= s5 goal)
)
