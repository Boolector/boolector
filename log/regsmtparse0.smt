(benchmark fuzz17788
 :logic QF_BV
 :formula
 (let (?e1 bv1[1])
  (let (?e2 bv0[1])
   (let (?E3 (= ?e2 ?e1))
    (let (?e4 (and ?e1 ?e3))
     (and true true)
     )))))
