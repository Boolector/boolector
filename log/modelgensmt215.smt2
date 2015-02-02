(set-logic QF_AUFBV)
(declare-fun a1 () (Array (_ BitVec 2) (_ BitVec 4)))
(define-fun $e2 () (_ BitVec 4) (_ bv0 4))
(define-fun f3 ((p4 (_ BitVec 2))) (_ BitVec 4)
 (let (($e5 ((_ extract 1 1) p4))) (let (($e6 ((_ extract 0 0) p4))) (let (($e7 (select a1 p4))) (let (($e8 (bvand $e5 $e6))) (let (($e9 (ite (= #b1 $e8) (bvnot $e2) $e7))) $e9))))))
(define-fun $e10 () (_ BitVec 1) ([btormain] CAUGHT SIGNAL 6
unknown
