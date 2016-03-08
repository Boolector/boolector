(benchmark smtlet.smt
 :logic QF_BV
 :extrapreds ((a))
 :formula (flet ($b a)(and a (not $b))))
