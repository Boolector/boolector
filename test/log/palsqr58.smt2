(set-logic QF_BV)
(declare-fun r () (_ BitVec 29))
(declare-fun s () (_ BitVec 58))
(assert (= s (bvmul ((_ zero_extend 29) r) ((_ zero_extend 29) r))))
(assert (= ((_ extract 57 57) s) ((_ extract  0  0) s)))
(assert (= ((_ extract 56 56) s) ((_ extract  1  1) s)))
(assert (= ((_ extract 55 55) s) ((_ extract  2  2) s)))
(assert (= ((_ extract 54 54) s) ((_ extract  3  3) s)))
(assert (= ((_ extract 53 53) s) ((_ extract  4  4) s)))
(assert (= ((_ extract 52 52) s) ((_ extract  5  5) s)))
(assert (= ((_ extract 51 51) s) ((_ extract  6  6) s)))
(assert (= ((_ extract 50 50) s) ((_ extract  7  7) s)))
(assert (= ((_ extract 49 49) s) ((_ extract  8  8) s)))
(assert (= ((_ extract 48 48) s) ((_ extract  9  9) s)))
(assert (= ((_ extract 47 47) s) ((_ extract 10 10) s)))
(assert (= ((_ extract 46 46) s) ((_ extract 11 11) s)))
(assert (= ((_ extract 45 45) s) ((_ extract 12 12) s)))
(assert (= ((_ extract 44 44) s) ((_ extract 13 13) s)))
(assert (= ((_ extract 43 43) s) ((_ extract 14 14) s)))
(assert (= ((_ extract 42 42) s) ((_ extract 15 15) s)))
(assert (= ((_ extract 41 41) s) ((_ extract 16 16) s)))
(assert (= ((_ extract 40 40) s) ((_ extract 17 17) s)))
(assert (= ((_ extract 39 39) s) ((_ extract 18 18) s)))
(assert (= ((_ extract 38 38) s) ((_ extract 19 19) s)))
(assert (= ((_ extract 37 37) s) ((_ extract 20 20) s)))
(assert (= ((_ extract 36 36) s) ((_ extract 21 21) s)))
(assert (= ((_ extract 35 35) s) ((_ extract 22 22) s)))
(assert (= ((_ extract 34 34) s) ((_ extract 23 23) s)))
(assert (= ((_ extract 33 33) s) ((_ extract 24 24) s)))
(assert (= ((_ extract 32 32) s) ((_ extract 25 25) s)))
(assert (= ((_ extract 31 31) s) ((_ extract 26 26) s)))
(assert (= ((_ extract 30 30) s) ((_ extract 27 27) s)))
(assert (= ((_ extract 29 29) s) ((_ extract 28 28) s)))

; assume the highest bit of 's' is set ...
;
(assert ((_ extract 57 57) s))

; ... or alternatively disallow the followin spurious solutions:
;
;(assert (distinct r #b00000000000000000000000000000))
;(assert (distinct r #b00011000100011000111101101000)) 	;(_ bv51482472 29)))
;

; then this is the only solution (uncomment to check that it is)
;
(assert (distinct r #b10111010000001011100111110001))	;(_ bv390117873 29)))

(check-sat)
(exit)
