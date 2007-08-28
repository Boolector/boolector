(benchmark smtandvar.smt
 :logic QF_BV
 :extrapreds ((a)(b))
 :formula (and (not a) (iff a b)))
