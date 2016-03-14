(set-logic QF_AUFBV)
(declare-fun v1 () (_ BitVec 4))
(declare-fun v2 () (_ BitVec 4))
(declare-fun v3 () (_ BitVec 4))
(declare-fun v4 () (_ BitVec 4))
(declare-fun a5 () (Array (_ BitVec 4) (_ BitVec 4)))
(declare-fun a6 () (Array (_ BitVec 4) (_ BitVec 4)))
(define-fun f7 ((p8 (_ BitVec 4))) (_ BitVec 4)
 (let (($e9 (ite (= v1 p8) #b1 #b0))) (let (($e10 (select a5 p8))) (let (($e11 (ite (= #b1 $e9) v2 $e10))) $e11))))
(define-fun f12 ((p13 (_ BitVec 4))) (_ BitVec 4)
 (let (($e14 (ite (= v3 p13) #b1 #b0))) (let (($e15 (select a6 p13))) (let (($e16 (ite (= #b1 $e14) v4 $e15))) $e16))))
(define-fun $e17 () (_ BitVec 1) ([btormain] CAUGHT SIGNAL 6
unknown
