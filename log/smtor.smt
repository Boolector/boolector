(benchmark smtandvar.smt
 :logic QF_BV
 :extrapreds ((a)(b))
 :formula (and (not a) (or a b)))
