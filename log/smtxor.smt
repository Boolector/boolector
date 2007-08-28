(benchmark smtandvar.smt
 :logic QF_BV
 :extrapreds ((a)(b))
 :formula (and a (xor a b)))
