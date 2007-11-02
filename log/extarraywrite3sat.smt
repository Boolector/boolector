(benchmark extarraywrite3
  :logic QF_AUFBV
  :extrafuns ((a Array[32:8]))
  :extrafuns ((i BitVec[32]))
  :extrafuns ((j BitVec[32]))
  :extrafuns ((ui BitVec[8]))
  :extrafuns ((uj BitVec[8]))
  :extrafuns ((vi BitVec[8]))
  :extrafuns ((vj BitVec[8]))
  ;:assumption (not (= i j))
  :assumption (= (store (store a i ui) j uj) (store (store a j vj) i vi))
  :formula (not (and (= ui vi) (= uj vj)))
)
