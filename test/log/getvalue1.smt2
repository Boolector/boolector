(set-option :produce-models true)
      (set-logic QF_BV)
      (declare-fun s0 () (_ BitVec 8))
      (check-sat)
      (get-value (s0))

