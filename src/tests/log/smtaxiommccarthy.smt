(benchmark smtaxiommccarthy
 :logic QF_AUFBV
 :extrafuns ((i BitVec[32]))
 :extrafuns ((j BitVec[32]))
 :extrafuns ((v BitVec[8]))
 :extrafuns ((a Array[32:8]))
 :formula
 (not
  (let (?b (store a i v))
   (= 
    (select ?b j)
    (ite 
     (= i j)
     v
     (select a j))))))
