(declare-fun a () (Array (_ BitVec 1) (_ BitVec 1)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 1)))
(assert (ite (_ bv1 1) a b)
