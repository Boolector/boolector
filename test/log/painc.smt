(benchmark root10
:logic QF_BV
:extrafuns ((x BitVec[32]))
:extrafuns ((next_x BitVec[32]))
:extrafuns ((n BitVec[32]))
:extrafuns ((one BitVec[32]))
:assumption (= one bv1[32])
:assumption (bvsge x n)
:assumption (= next_x (bvadd x one))
:formula (bvslt next_x n)
:formula (bvsge next_x n))
