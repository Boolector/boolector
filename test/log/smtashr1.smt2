(set-option :incremental false)
(set-logic QF_BV)
(assert (= (bvashr (_ bv0 1) (_ bv0 1)) (_ bv0 1)))
(assert (= (bvashr (_ bv0 1) (_ bv1 1)) (_ bv0 1)))
(assert (= (bvashr (_ bv1 1) (_ bv0 1)) (_ bv1 1)))
(assert (= (bvashr (_ bv1 1) (_ bv1 1)) (_ bv1 1)))
(check-sat)

