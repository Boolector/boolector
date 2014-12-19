(set-logic QF_AUFBV)
(declare-fun a1 () (Array (_ BitVec 1) (_ BitVec 1)))
(declare-fun a2 () (Array (_ BitVec 1) (_ BitVec 1)))
(define-fun $e3 () (_ BitVec 1) (_ bv0 1))
(define-fun $e4 () (_ BitVec 1) (select a1 $e3))
(define-fun $e5 () (_ BitVec 1) (select a1 (bvnot $e3)))
(define-fun $e6 () (_ BitVec 1) (select a2 $e3))
(define-fun $e7 () (_ BitVec 1) ([btormain] CAUGHT SIGNAL 6
unknown
