
(set-logic QF_BV)
(declare-fun s () (_ BitVec 4))
(declare-fun t () (_ BitVec 4))
(assert (let ((_let_0 ((_ extract 3 3) s))) (let ((_let_1 ((_ extract 3 3) t))) (not (= (bvsle s t) (or (and (= _let_0 (_ bv1 1)) (= _let_1 (_ bv0 1))) (and (= _let_0 _let_1) (bvule s t))))))))
(check-sat)
(exit)
