(set-option :incremental false)
(set-info :status unknown)
(set-logic QF_AUFBV)
(declare-fun v3 () (_ BitVec 4))
(declare-fun v2 () (_ BitVec 1))
(assert (not (= (bvlshr (bvxor v3 ((_ zero_extend 3) v2)) ((_ rotate_left 3) v3)) (_ bv0 4))))
(check-sat)

