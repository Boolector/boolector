(set-option :incremental false)
(set-logic QF_BV)
(assert (= (bvlshr (_ bv0 1) (_ bv0 1)) (_ bv0 1)))
(assert (= (bvlshr (_ bv0 1) (_ bv1 1)) (_ bv0 1)))
(assert (= (bvlshr (_ bv1 1) (_ bv0 1)) (_ bv1 1)))
(assert (= (bvlshr (_ bv1 1) (_ bv1 1)) (_ bv0 1)))
(check-sat)

