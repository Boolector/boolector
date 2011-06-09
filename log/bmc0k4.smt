(benchmark bmc
:source {
  Armin Biere, FMV, JKU, June, 2011.

  Incremental example, assumptions are added eagerly.

  Formulas are only checked individually and not asserted permanently
  Start with all bits zero state.

  To have the incremental idea working uncomment the
  commented ':formula' lines.  You also need support
  from your SMT solver for that.

  Toggle at most one bit per step using the Hacker Delight trick
  '(x & (x-1)) == 0' iff x has exactly one bit set.

  This is enforced for the difference between two consecutive states.
}
:logic QF_BV
;------------------------------------ bad
:extrafuns ((goal BitVec[4]))
:assumption (= goal bv15[4])
;------------------------------------ global
:extrafuns ((zero BitVec[4]))
:extrafuns ((one BitVec[4]))
:assumption (= zero bv0[4])
:assumption (= one bv1[4])
;------------------------------------ s0
:extrafuns ((s0 BitVec[4]))
:assumption (= s0 zero);
:formula (= s0 goal)
;------------------------------------ s1
:extrafuns ((s1 BitVec[4]))
:assumption (let (?d1 (bvsub s1 s0)) (= (bvand ?d1 (bvsub ?d1 one)) zero))
:formula (= s1 goal)                     
;------------------------------------ s2
:extrafuns ((s2 BitVec[4]))
; For a change we use a globally visible variable instead of let
; which would actually more efficient.  The variable is in scope
; for the rest of the file.  So to me it seems better to encode
; all the next state and checking logic only with 'let'.
:extrafuns ((d2 BitVec[4]))
:assumption (= d2 (bvsub s2 s1))
:assumption (= (bvand d2 (bvsub d2 one)) zero)
:formula (= s2 goal)
;------------------------------------ s3
:extrafuns ((s3 BitVec[4]))
:assumption (let (?d3 (bvsub s3 s2)) (= (bvand ?d3 (bvsub ?d3 one)) zero))
:formula (= s3 goal)                     
;------------------------------------ s4
:extrafuns ((s4 BitVec[4]))
:assumption (let (?d4 (bvsub s4 s3)) (= (bvand ?d4 (bvsub ?d4 one)) zero))
:formula (= s4 goal)                     
)
