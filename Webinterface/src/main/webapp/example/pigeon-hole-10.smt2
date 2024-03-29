; Boolean Pigeon Hole Problem in SMT format
;
; Variables p_n_i_j states pigeon i sits in hole j
;   where n is number of holes, 0<=i<=n, 1<=j<=n
; Clauses are
;   (or p_n_i_1 ... p_n_i_n)   for  0<=i<=n.
;     (every pigeon sits in a hole)
;   (or (not p_n_i_j) (not p_n_i'_j)) for 0<=i<i'<=n,1<=j<=n
;     (no two pigeons sit in the same hole

(set-option :produce-proofs true)
(set-logic QF_UF)
(declare-fun p_10_0_1 () Bool)
(declare-fun p_10_0_2 () Bool)
(declare-fun p_10_0_3 () Bool)
(declare-fun p_10_0_4 () Bool)
(declare-fun p_10_0_5 () Bool)
(declare-fun p_10_0_6 () Bool)
(declare-fun p_10_0_7 () Bool)
(declare-fun p_10_0_8 () Bool)
(declare-fun p_10_0_9 () Bool)
(declare-fun p_10_0_10 () Bool)
(declare-fun p_10_1_1 () Bool)
(declare-fun p_10_1_2 () Bool)
(declare-fun p_10_1_3 () Bool)
(declare-fun p_10_1_4 () Bool)
(declare-fun p_10_1_5 () Bool)
(declare-fun p_10_1_6 () Bool)
(declare-fun p_10_1_7 () Bool)
(declare-fun p_10_1_8 () Bool)
(declare-fun p_10_1_9 () Bool)
(declare-fun p_10_1_10 () Bool)
(declare-fun p_10_2_1 () Bool)
(declare-fun p_10_2_2 () Bool)
(declare-fun p_10_2_3 () Bool)
(declare-fun p_10_2_4 () Bool)
(declare-fun p_10_2_5 () Bool)
(declare-fun p_10_2_6 () Bool)
(declare-fun p_10_2_7 () Bool)
(declare-fun p_10_2_8 () Bool)
(declare-fun p_10_2_9 () Bool)
(declare-fun p_10_2_10 () Bool)
(declare-fun p_10_3_1 () Bool)
(declare-fun p_10_3_2 () Bool)
(declare-fun p_10_3_3 () Bool)
(declare-fun p_10_3_4 () Bool)
(declare-fun p_10_3_5 () Bool)
(declare-fun p_10_3_6 () Bool)
(declare-fun p_10_3_7 () Bool)
(declare-fun p_10_3_8 () Bool)
(declare-fun p_10_3_9 () Bool)
(declare-fun p_10_3_10 () Bool)
(declare-fun p_10_4_1 () Bool)
(declare-fun p_10_4_2 () Bool)
(declare-fun p_10_4_3 () Bool)
(declare-fun p_10_4_4 () Bool)
(declare-fun p_10_4_5 () Bool)
(declare-fun p_10_4_6 () Bool)
(declare-fun p_10_4_7 () Bool)
(declare-fun p_10_4_8 () Bool)
(declare-fun p_10_4_9 () Bool)
(declare-fun p_10_4_10 () Bool)
(declare-fun p_10_5_1 () Bool)
(declare-fun p_10_5_2 () Bool)
(declare-fun p_10_5_3 () Bool)
(declare-fun p_10_5_4 () Bool)
(declare-fun p_10_5_5 () Bool)
(declare-fun p_10_5_6 () Bool)
(declare-fun p_10_5_7 () Bool)
(declare-fun p_10_5_8 () Bool)
(declare-fun p_10_5_9 () Bool)
(declare-fun p_10_5_10 () Bool)
(declare-fun p_10_6_1 () Bool)
(declare-fun p_10_6_2 () Bool)
(declare-fun p_10_6_3 () Bool)
(declare-fun p_10_6_4 () Bool)
(declare-fun p_10_6_5 () Bool)
(declare-fun p_10_6_6 () Bool)
(declare-fun p_10_6_7 () Bool)
(declare-fun p_10_6_8 () Bool)
(declare-fun p_10_6_9 () Bool)
(declare-fun p_10_6_10 () Bool)
(declare-fun p_10_7_1 () Bool)
(declare-fun p_10_7_2 () Bool)
(declare-fun p_10_7_3 () Bool)
(declare-fun p_10_7_4 () Bool)
(declare-fun p_10_7_5 () Bool)
(declare-fun p_10_7_6 () Bool)
(declare-fun p_10_7_7 () Bool)
(declare-fun p_10_7_8 () Bool)
(declare-fun p_10_7_9 () Bool)
(declare-fun p_10_7_10 () Bool)
(declare-fun p_10_8_1 () Bool)
(declare-fun p_10_8_2 () Bool)
(declare-fun p_10_8_3 () Bool)
(declare-fun p_10_8_4 () Bool)
(declare-fun p_10_8_5 () Bool)
(declare-fun p_10_8_6 () Bool)
(declare-fun p_10_8_7 () Bool)
(declare-fun p_10_8_8 () Bool)
(declare-fun p_10_8_9 () Bool)
(declare-fun p_10_8_10 () Bool)
(declare-fun p_10_9_1 () Bool)
(declare-fun p_10_9_2 () Bool)
(declare-fun p_10_9_3 () Bool)
(declare-fun p_10_9_4 () Bool)
(declare-fun p_10_9_5 () Bool)
(declare-fun p_10_9_6 () Bool)
(declare-fun p_10_9_7 () Bool)
(declare-fun p_10_9_8 () Bool)
(declare-fun p_10_9_9 () Bool)
(declare-fun p_10_9_10 () Bool)
(declare-fun p_10_10_1 () Bool)
(declare-fun p_10_10_2 () Bool)
(declare-fun p_10_10_3 () Bool)
(declare-fun p_10_10_4 () Bool)
(declare-fun p_10_10_5 () Bool)
(declare-fun p_10_10_6 () Bool)
(declare-fun p_10_10_7 () Bool)
(declare-fun p_10_10_8 () Bool)
(declare-fun p_10_10_9 () Bool)
(declare-fun p_10_10_10 () Bool)
(assert (or p_10_0_1 p_10_0_2 p_10_0_3 p_10_0_4 p_10_0_5 p_10_0_6 p_10_0_7 p_10_0_8 p_10_0_9 p_10_0_10))
(assert (or p_10_1_1 p_10_1_2 p_10_1_3 p_10_1_4 p_10_1_5 p_10_1_6 p_10_1_7 p_10_1_8 p_10_1_9 p_10_1_10))
(assert (or p_10_2_1 p_10_2_2 p_10_2_3 p_10_2_4 p_10_2_5 p_10_2_6 p_10_2_7 p_10_2_8 p_10_2_9 p_10_2_10))
(assert (or p_10_3_1 p_10_3_2 p_10_3_3 p_10_3_4 p_10_3_5 p_10_3_6 p_10_3_7 p_10_3_8 p_10_3_9 p_10_3_10))
(assert (or p_10_4_1 p_10_4_2 p_10_4_3 p_10_4_4 p_10_4_5 p_10_4_6 p_10_4_7 p_10_4_8 p_10_4_9 p_10_4_10))
(assert (or p_10_5_1 p_10_5_2 p_10_5_3 p_10_5_4 p_10_5_5 p_10_5_6 p_10_5_7 p_10_5_8 p_10_5_9 p_10_5_10))
(assert (or p_10_6_1 p_10_6_2 p_10_6_3 p_10_6_4 p_10_6_5 p_10_6_6 p_10_6_7 p_10_6_8 p_10_6_9 p_10_6_10))
(assert (or p_10_7_1 p_10_7_2 p_10_7_3 p_10_7_4 p_10_7_5 p_10_7_6 p_10_7_7 p_10_7_8 p_10_7_9 p_10_7_10))
(assert (or p_10_8_1 p_10_8_2 p_10_8_3 p_10_8_4 p_10_8_5 p_10_8_6 p_10_8_7 p_10_8_8 p_10_8_9 p_10_8_10))
(assert (or p_10_9_1 p_10_9_2 p_10_9_3 p_10_9_4 p_10_9_5 p_10_9_6 p_10_9_7 p_10_9_8 p_10_9_9 p_10_9_10))
(assert (or p_10_10_1 p_10_10_2 p_10_10_3 p_10_10_4 p_10_10_5 p_10_10_6 p_10_10_7 p_10_10_8 p_10_10_9 p_10_10_10))
(assert (or (not p_10_0_1) (not p_10_1_1)))
(assert (or (not p_10_0_2) (not p_10_1_2)))
(assert (or (not p_10_0_3) (not p_10_1_3)))
(assert (or (not p_10_0_4) (not p_10_1_4)))
(assert (or (not p_10_0_5) (not p_10_1_5)))
(assert (or (not p_10_0_6) (not p_10_1_6)))
(assert (or (not p_10_0_7) (not p_10_1_7)))
(assert (or (not p_10_0_8) (not p_10_1_8)))
(assert (or (not p_10_0_9) (not p_10_1_9)))
(assert (or (not p_10_0_10) (not p_10_1_10)))
(assert (or (not p_10_0_1) (not p_10_2_1)))
(assert (or (not p_10_0_2) (not p_10_2_2)))
(assert (or (not p_10_0_3) (not p_10_2_3)))
(assert (or (not p_10_0_4) (not p_10_2_4)))
(assert (or (not p_10_0_5) (not p_10_2_5)))
(assert (or (not p_10_0_6) (not p_10_2_6)))
(assert (or (not p_10_0_7) (not p_10_2_7)))
(assert (or (not p_10_0_8) (not p_10_2_8)))
(assert (or (not p_10_0_9) (not p_10_2_9)))
(assert (or (not p_10_0_10) (not p_10_2_10)))
(assert (or (not p_10_0_1) (not p_10_3_1)))
(assert (or (not p_10_0_2) (not p_10_3_2)))
(assert (or (not p_10_0_3) (not p_10_3_3)))
(assert (or (not p_10_0_4) (not p_10_3_4)))
(assert (or (not p_10_0_5) (not p_10_3_5)))
(assert (or (not p_10_0_6) (not p_10_3_6)))
(assert (or (not p_10_0_7) (not p_10_3_7)))
(assert (or (not p_10_0_8) (not p_10_3_8)))
(assert (or (not p_10_0_9) (not p_10_3_9)))
(assert (or (not p_10_0_10) (not p_10_3_10)))
(assert (or (not p_10_0_1) (not p_10_4_1)))
(assert (or (not p_10_0_2) (not p_10_4_2)))
(assert (or (not p_10_0_3) (not p_10_4_3)))
(assert (or (not p_10_0_4) (not p_10_4_4)))
(assert (or (not p_10_0_5) (not p_10_4_5)))
(assert (or (not p_10_0_6) (not p_10_4_6)))
(assert (or (not p_10_0_7) (not p_10_4_7)))
(assert (or (not p_10_0_8) (not p_10_4_8)))
(assert (or (not p_10_0_9) (not p_10_4_9)))
(assert (or (not p_10_0_10) (not p_10_4_10)))
(assert (or (not p_10_0_1) (not p_10_5_1)))
(assert (or (not p_10_0_2) (not p_10_5_2)))
(assert (or (not p_10_0_3) (not p_10_5_3)))
(assert (or (not p_10_0_4) (not p_10_5_4)))
(assert (or (not p_10_0_5) (not p_10_5_5)))
(assert (or (not p_10_0_6) (not p_10_5_6)))
(assert (or (not p_10_0_7) (not p_10_5_7)))
(assert (or (not p_10_0_8) (not p_10_5_8)))
(assert (or (not p_10_0_9) (not p_10_5_9)))
(assert (or (not p_10_0_10) (not p_10_5_10)))
(assert (or (not p_10_0_1) (not p_10_6_1)))
(assert (or (not p_10_0_2) (not p_10_6_2)))
(assert (or (not p_10_0_3) (not p_10_6_3)))
(assert (or (not p_10_0_4) (not p_10_6_4)))
(assert (or (not p_10_0_5) (not p_10_6_5)))
(assert (or (not p_10_0_6) (not p_10_6_6)))
(assert (or (not p_10_0_7) (not p_10_6_7)))
(assert (or (not p_10_0_8) (not p_10_6_8)))
(assert (or (not p_10_0_9) (not p_10_6_9)))
(assert (or (not p_10_0_10) (not p_10_6_10)))
(assert (or (not p_10_0_1) (not p_10_7_1)))
(assert (or (not p_10_0_2) (not p_10_7_2)))
(assert (or (not p_10_0_3) (not p_10_7_3)))
(assert (or (not p_10_0_4) (not p_10_7_4)))
(assert (or (not p_10_0_5) (not p_10_7_5)))
(assert (or (not p_10_0_6) (not p_10_7_6)))
(assert (or (not p_10_0_7) (not p_10_7_7)))
(assert (or (not p_10_0_8) (not p_10_7_8)))
(assert (or (not p_10_0_9) (not p_10_7_9)))
(assert (or (not p_10_0_10) (not p_10_7_10)))
(assert (or (not p_10_0_1) (not p_10_8_1)))
(assert (or (not p_10_0_2) (not p_10_8_2)))
(assert (or (not p_10_0_3) (not p_10_8_3)))
(assert (or (not p_10_0_4) (not p_10_8_4)))
(assert (or (not p_10_0_5) (not p_10_8_5)))
(assert (or (not p_10_0_6) (not p_10_8_6)))
(assert (or (not p_10_0_7) (not p_10_8_7)))
(assert (or (not p_10_0_8) (not p_10_8_8)))
(assert (or (not p_10_0_9) (not p_10_8_9)))
(assert (or (not p_10_0_10) (not p_10_8_10)))
(assert (or (not p_10_0_1) (not p_10_9_1)))
(assert (or (not p_10_0_2) (not p_10_9_2)))
(assert (or (not p_10_0_3) (not p_10_9_3)))
(assert (or (not p_10_0_4) (not p_10_9_4)))
(assert (or (not p_10_0_5) (not p_10_9_5)))
(assert (or (not p_10_0_6) (not p_10_9_6)))
(assert (or (not p_10_0_7) (not p_10_9_7)))
(assert (or (not p_10_0_8) (not p_10_9_8)))
(assert (or (not p_10_0_9) (not p_10_9_9)))
(assert (or (not p_10_0_10) (not p_10_9_10)))
(assert (or (not p_10_0_1) (not p_10_10_1)))
(assert (or (not p_10_0_2) (not p_10_10_2)))
(assert (or (not p_10_0_3) (not p_10_10_3)))
(assert (or (not p_10_0_4) (not p_10_10_4)))
(assert (or (not p_10_0_5) (not p_10_10_5)))
(assert (or (not p_10_0_6) (not p_10_10_6)))
(assert (or (not p_10_0_7) (not p_10_10_7)))
(assert (or (not p_10_0_8) (not p_10_10_8)))
(assert (or (not p_10_0_9) (not p_10_10_9)))
(assert (or (not p_10_0_10) (not p_10_10_10)))
(assert (or (not p_10_1_1) (not p_10_2_1)))
(assert (or (not p_10_1_2) (not p_10_2_2)))
(assert (or (not p_10_1_3) (not p_10_2_3)))
(assert (or (not p_10_1_4) (not p_10_2_4)))
(assert (or (not p_10_1_5) (not p_10_2_5)))
(assert (or (not p_10_1_6) (not p_10_2_6)))
(assert (or (not p_10_1_7) (not p_10_2_7)))
(assert (or (not p_10_1_8) (not p_10_2_8)))
(assert (or (not p_10_1_9) (not p_10_2_9)))
(assert (or (not p_10_1_10) (not p_10_2_10)))
(assert (or (not p_10_1_1) (not p_10_3_1)))
(assert (or (not p_10_1_2) (not p_10_3_2)))
(assert (or (not p_10_1_3) (not p_10_3_3)))
(assert (or (not p_10_1_4) (not p_10_3_4)))
(assert (or (not p_10_1_5) (not p_10_3_5)))
(assert (or (not p_10_1_6) (not p_10_3_6)))
(assert (or (not p_10_1_7) (not p_10_3_7)))
(assert (or (not p_10_1_8) (not p_10_3_8)))
(assert (or (not p_10_1_9) (not p_10_3_9)))
(assert (or (not p_10_1_10) (not p_10_3_10)))
(assert (or (not p_10_1_1) (not p_10_4_1)))
(assert (or (not p_10_1_2) (not p_10_4_2)))
(assert (or (not p_10_1_3) (not p_10_4_3)))
(assert (or (not p_10_1_4) (not p_10_4_4)))
(assert (or (not p_10_1_5) (not p_10_4_5)))
(assert (or (not p_10_1_6) (not p_10_4_6)))
(assert (or (not p_10_1_7) (not p_10_4_7)))
(assert (or (not p_10_1_8) (not p_10_4_8)))
(assert (or (not p_10_1_9) (not p_10_4_9)))
(assert (or (not p_10_1_10) (not p_10_4_10)))
(assert (or (not p_10_1_1) (not p_10_5_1)))
(assert (or (not p_10_1_2) (not p_10_5_2)))
(assert (or (not p_10_1_3) (not p_10_5_3)))
(assert (or (not p_10_1_4) (not p_10_5_4)))
(assert (or (not p_10_1_5) (not p_10_5_5)))
(assert (or (not p_10_1_6) (not p_10_5_6)))
(assert (or (not p_10_1_7) (not p_10_5_7)))
(assert (or (not p_10_1_8) (not p_10_5_8)))
(assert (or (not p_10_1_9) (not p_10_5_9)))
(assert (or (not p_10_1_10) (not p_10_5_10)))
(assert (or (not p_10_1_1) (not p_10_6_1)))
(assert (or (not p_10_1_2) (not p_10_6_2)))
(assert (or (not p_10_1_3) (not p_10_6_3)))
(assert (or (not p_10_1_4) (not p_10_6_4)))
(assert (or (not p_10_1_5) (not p_10_6_5)))
(assert (or (not p_10_1_6) (not p_10_6_6)))
(assert (or (not p_10_1_7) (not p_10_6_7)))
(assert (or (not p_10_1_8) (not p_10_6_8)))
(assert (or (not p_10_1_9) (not p_10_6_9)))
(assert (or (not p_10_1_10) (not p_10_6_10)))
(assert (or (not p_10_1_1) (not p_10_7_1)))
(assert (or (not p_10_1_2) (not p_10_7_2)))
(assert (or (not p_10_1_3) (not p_10_7_3)))
(assert (or (not p_10_1_4) (not p_10_7_4)))
(assert (or (not p_10_1_5) (not p_10_7_5)))
(assert (or (not p_10_1_6) (not p_10_7_6)))
(assert (or (not p_10_1_7) (not p_10_7_7)))
(assert (or (not p_10_1_8) (not p_10_7_8)))
(assert (or (not p_10_1_9) (not p_10_7_9)))
(assert (or (not p_10_1_10) (not p_10_7_10)))
(assert (or (not p_10_1_1) (not p_10_8_1)))
(assert (or (not p_10_1_2) (not p_10_8_2)))
(assert (or (not p_10_1_3) (not p_10_8_3)))
(assert (or (not p_10_1_4) (not p_10_8_4)))
(assert (or (not p_10_1_5) (not p_10_8_5)))
(assert (or (not p_10_1_6) (not p_10_8_6)))
(assert (or (not p_10_1_7) (not p_10_8_7)))
(assert (or (not p_10_1_8) (not p_10_8_8)))
(assert (or (not p_10_1_9) (not p_10_8_9)))
(assert (or (not p_10_1_10) (not p_10_8_10)))
(assert (or (not p_10_1_1) (not p_10_9_1)))
(assert (or (not p_10_1_2) (not p_10_9_2)))
(assert (or (not p_10_1_3) (not p_10_9_3)))
(assert (or (not p_10_1_4) (not p_10_9_4)))
(assert (or (not p_10_1_5) (not p_10_9_5)))
(assert (or (not p_10_1_6) (not p_10_9_6)))
(assert (or (not p_10_1_7) (not p_10_9_7)))
(assert (or (not p_10_1_8) (not p_10_9_8)))
(assert (or (not p_10_1_9) (not p_10_9_9)))
(assert (or (not p_10_1_10) (not p_10_9_10)))
(assert (or (not p_10_1_1) (not p_10_10_1)))
(assert (or (not p_10_1_2) (not p_10_10_2)))
(assert (or (not p_10_1_3) (not p_10_10_3)))
(assert (or (not p_10_1_4) (not p_10_10_4)))
(assert (or (not p_10_1_5) (not p_10_10_5)))
(assert (or (not p_10_1_6) (not p_10_10_6)))
(assert (or (not p_10_1_7) (not p_10_10_7)))
(assert (or (not p_10_1_8) (not p_10_10_8)))
(assert (or (not p_10_1_9) (not p_10_10_9)))
(assert (or (not p_10_1_10) (not p_10_10_10)))
(assert (or (not p_10_2_1) (not p_10_3_1)))
(assert (or (not p_10_2_2) (not p_10_3_2)))
(assert (or (not p_10_2_3) (not p_10_3_3)))
(assert (or (not p_10_2_4) (not p_10_3_4)))
(assert (or (not p_10_2_5) (not p_10_3_5)))
(assert (or (not p_10_2_6) (not p_10_3_6)))
(assert (or (not p_10_2_7) (not p_10_3_7)))
(assert (or (not p_10_2_8) (not p_10_3_8)))
(assert (or (not p_10_2_9) (not p_10_3_9)))
(assert (or (not p_10_2_10) (not p_10_3_10)))
(assert (or (not p_10_2_1) (not p_10_4_1)))
(assert (or (not p_10_2_2) (not p_10_4_2)))
(assert (or (not p_10_2_3) (not p_10_4_3)))
(assert (or (not p_10_2_4) (not p_10_4_4)))
(assert (or (not p_10_2_5) (not p_10_4_5)))
(assert (or (not p_10_2_6) (not p_10_4_6)))
(assert (or (not p_10_2_7) (not p_10_4_7)))
(assert (or (not p_10_2_8) (not p_10_4_8)))
(assert (or (not p_10_2_9) (not p_10_4_9)))
(assert (or (not p_10_2_10) (not p_10_4_10)))
(assert (or (not p_10_2_1) (not p_10_5_1)))
(assert (or (not p_10_2_2) (not p_10_5_2)))
(assert (or (not p_10_2_3) (not p_10_5_3)))
(assert (or (not p_10_2_4) (not p_10_5_4)))
(assert (or (not p_10_2_5) (not p_10_5_5)))
(assert (or (not p_10_2_6) (not p_10_5_6)))
(assert (or (not p_10_2_7) (not p_10_5_7)))
(assert (or (not p_10_2_8) (not p_10_5_8)))
(assert (or (not p_10_2_9) (not p_10_5_9)))
(assert (or (not p_10_2_10) (not p_10_5_10)))
(assert (or (not p_10_2_1) (not p_10_6_1)))
(assert (or (not p_10_2_2) (not p_10_6_2)))
(assert (or (not p_10_2_3) (not p_10_6_3)))
(assert (or (not p_10_2_4) (not p_10_6_4)))
(assert (or (not p_10_2_5) (not p_10_6_5)))
(assert (or (not p_10_2_6) (not p_10_6_6)))
(assert (or (not p_10_2_7) (not p_10_6_7)))
(assert (or (not p_10_2_8) (not p_10_6_8)))
(assert (or (not p_10_2_9) (not p_10_6_9)))
(assert (or (not p_10_2_10) (not p_10_6_10)))
(assert (or (not p_10_2_1) (not p_10_7_1)))
(assert (or (not p_10_2_2) (not p_10_7_2)))
(assert (or (not p_10_2_3) (not p_10_7_3)))
(assert (or (not p_10_2_4) (not p_10_7_4)))
(assert (or (not p_10_2_5) (not p_10_7_5)))
(assert (or (not p_10_2_6) (not p_10_7_6)))
(assert (or (not p_10_2_7) (not p_10_7_7)))
(assert (or (not p_10_2_8) (not p_10_7_8)))
(assert (or (not p_10_2_9) (not p_10_7_9)))
(assert (or (not p_10_2_10) (not p_10_7_10)))
(assert (or (not p_10_2_1) (not p_10_8_1)))
(assert (or (not p_10_2_2) (not p_10_8_2)))
(assert (or (not p_10_2_3) (not p_10_8_3)))
(assert (or (not p_10_2_4) (not p_10_8_4)))
(assert (or (not p_10_2_5) (not p_10_8_5)))
(assert (or (not p_10_2_6) (not p_10_8_6)))
(assert (or (not p_10_2_7) (not p_10_8_7)))
(assert (or (not p_10_2_8) (not p_10_8_8)))
(assert (or (not p_10_2_9) (not p_10_8_9)))
(assert (or (not p_10_2_10) (not p_10_8_10)))
(assert (or (not p_10_2_1) (not p_10_9_1)))
(assert (or (not p_10_2_2) (not p_10_9_2)))
(assert (or (not p_10_2_3) (not p_10_9_3)))
(assert (or (not p_10_2_4) (not p_10_9_4)))
(assert (or (not p_10_2_5) (not p_10_9_5)))
(assert (or (not p_10_2_6) (not p_10_9_6)))
(assert (or (not p_10_2_7) (not p_10_9_7)))
(assert (or (not p_10_2_8) (not p_10_9_8)))
(assert (or (not p_10_2_9) (not p_10_9_9)))
(assert (or (not p_10_2_10) (not p_10_9_10)))
(assert (or (not p_10_2_1) (not p_10_10_1)))
(assert (or (not p_10_2_2) (not p_10_10_2)))
(assert (or (not p_10_2_3) (not p_10_10_3)))
(assert (or (not p_10_2_4) (not p_10_10_4)))
(assert (or (not p_10_2_5) (not p_10_10_5)))
(assert (or (not p_10_2_6) (not p_10_10_6)))
(assert (or (not p_10_2_7) (not p_10_10_7)))
(assert (or (not p_10_2_8) (not p_10_10_8)))
(assert (or (not p_10_2_9) (not p_10_10_9)))
(assert (or (not p_10_2_10) (not p_10_10_10)))
(assert (or (not p_10_3_1) (not p_10_4_1)))
(assert (or (not p_10_3_2) (not p_10_4_2)))
(assert (or (not p_10_3_3) (not p_10_4_3)))
(assert (or (not p_10_3_4) (not p_10_4_4)))
(assert (or (not p_10_3_5) (not p_10_4_5)))
(assert (or (not p_10_3_6) (not p_10_4_6)))
(assert (or (not p_10_3_7) (not p_10_4_7)))
(assert (or (not p_10_3_8) (not p_10_4_8)))
(assert (or (not p_10_3_9) (not p_10_4_9)))
(assert (or (not p_10_3_10) (not p_10_4_10)))
(assert (or (not p_10_3_1) (not p_10_5_1)))
(assert (or (not p_10_3_2) (not p_10_5_2)))
(assert (or (not p_10_3_3) (not p_10_5_3)))
(assert (or (not p_10_3_4) (not p_10_5_4)))
(assert (or (not p_10_3_5) (not p_10_5_5)))
(assert (or (not p_10_3_6) (not p_10_5_6)))
(assert (or (not p_10_3_7) (not p_10_5_7)))
(assert (or (not p_10_3_8) (not p_10_5_8)))
(assert (or (not p_10_3_9) (not p_10_5_9)))
(assert (or (not p_10_3_10) (not p_10_5_10)))
(assert (or (not p_10_3_1) (not p_10_6_1)))
(assert (or (not p_10_3_2) (not p_10_6_2)))
(assert (or (not p_10_3_3) (not p_10_6_3)))
(assert (or (not p_10_3_4) (not p_10_6_4)))
(assert (or (not p_10_3_5) (not p_10_6_5)))
(assert (or (not p_10_3_6) (not p_10_6_6)))
(assert (or (not p_10_3_7) (not p_10_6_7)))
(assert (or (not p_10_3_8) (not p_10_6_8)))
(assert (or (not p_10_3_9) (not p_10_6_9)))
(assert (or (not p_10_3_10) (not p_10_6_10)))
(assert (or (not p_10_3_1) (not p_10_7_1)))
(assert (or (not p_10_3_2) (not p_10_7_2)))
(assert (or (not p_10_3_3) (not p_10_7_3)))
(assert (or (not p_10_3_4) (not p_10_7_4)))
(assert (or (not p_10_3_5) (not p_10_7_5)))
(assert (or (not p_10_3_6) (not p_10_7_6)))
(assert (or (not p_10_3_7) (not p_10_7_7)))
(assert (or (not p_10_3_8) (not p_10_7_8)))
(assert (or (not p_10_3_9) (not p_10_7_9)))
(assert (or (not p_10_3_10) (not p_10_7_10)))
(assert (or (not p_10_3_1) (not p_10_8_1)))
(assert (or (not p_10_3_2) (not p_10_8_2)))
(assert (or (not p_10_3_3) (not p_10_8_3)))
(assert (or (not p_10_3_4) (not p_10_8_4)))
(assert (or (not p_10_3_5) (not p_10_8_5)))
(assert (or (not p_10_3_6) (not p_10_8_6)))
(assert (or (not p_10_3_7) (not p_10_8_7)))
(assert (or (not p_10_3_8) (not p_10_8_8)))
(assert (or (not p_10_3_9) (not p_10_8_9)))
(assert (or (not p_10_3_10) (not p_10_8_10)))
(assert (or (not p_10_3_1) (not p_10_9_1)))
(assert (or (not p_10_3_2) (not p_10_9_2)))
(assert (or (not p_10_3_3) (not p_10_9_3)))
(assert (or (not p_10_3_4) (not p_10_9_4)))
(assert (or (not p_10_3_5) (not p_10_9_5)))
(assert (or (not p_10_3_6) (not p_10_9_6)))
(assert (or (not p_10_3_7) (not p_10_9_7)))
(assert (or (not p_10_3_8) (not p_10_9_8)))
(assert (or (not p_10_3_9) (not p_10_9_9)))
(assert (or (not p_10_3_10) (not p_10_9_10)))
(assert (or (not p_10_3_1) (not p_10_10_1)))
(assert (or (not p_10_3_2) (not p_10_10_2)))
(assert (or (not p_10_3_3) (not p_10_10_3)))
(assert (or (not p_10_3_4) (not p_10_10_4)))
(assert (or (not p_10_3_5) (not p_10_10_5)))
(assert (or (not p_10_3_6) (not p_10_10_6)))
(assert (or (not p_10_3_7) (not p_10_10_7)))
(assert (or (not p_10_3_8) (not p_10_10_8)))
(assert (or (not p_10_3_9) (not p_10_10_9)))
(assert (or (not p_10_3_10) (not p_10_10_10)))
(assert (or (not p_10_4_1) (not p_10_5_1)))
(assert (or (not p_10_4_2) (not p_10_5_2)))
(assert (or (not p_10_4_3) (not p_10_5_3)))
(assert (or (not p_10_4_4) (not p_10_5_4)))
(assert (or (not p_10_4_5) (not p_10_5_5)))
(assert (or (not p_10_4_6) (not p_10_5_6)))
(assert (or (not p_10_4_7) (not p_10_5_7)))
(assert (or (not p_10_4_8) (not p_10_5_8)))
(assert (or (not p_10_4_9) (not p_10_5_9)))
(assert (or (not p_10_4_10) (not p_10_5_10)))
(assert (or (not p_10_4_1) (not p_10_6_1)))
(assert (or (not p_10_4_2) (not p_10_6_2)))
(assert (or (not p_10_4_3) (not p_10_6_3)))
(assert (or (not p_10_4_4) (not p_10_6_4)))
(assert (or (not p_10_4_5) (not p_10_6_5)))
(assert (or (not p_10_4_6) (not p_10_6_6)))
(assert (or (not p_10_4_7) (not p_10_6_7)))
(assert (or (not p_10_4_8) (not p_10_6_8)))
(assert (or (not p_10_4_9) (not p_10_6_9)))
(assert (or (not p_10_4_10) (not p_10_6_10)))
(assert (or (not p_10_4_1) (not p_10_7_1)))
(assert (or (not p_10_4_2) (not p_10_7_2)))
(assert (or (not p_10_4_3) (not p_10_7_3)))
(assert (or (not p_10_4_4) (not p_10_7_4)))
(assert (or (not p_10_4_5) (not p_10_7_5)))
(assert (or (not p_10_4_6) (not p_10_7_6)))
(assert (or (not p_10_4_7) (not p_10_7_7)))
(assert (or (not p_10_4_8) (not p_10_7_8)))
(assert (or (not p_10_4_9) (not p_10_7_9)))
(assert (or (not p_10_4_10) (not p_10_7_10)))
(assert (or (not p_10_4_1) (not p_10_8_1)))
(assert (or (not p_10_4_2) (not p_10_8_2)))
(assert (or (not p_10_4_3) (not p_10_8_3)))
(assert (or (not p_10_4_4) (not p_10_8_4)))
(assert (or (not p_10_4_5) (not p_10_8_5)))
(assert (or (not p_10_4_6) (not p_10_8_6)))
(assert (or (not p_10_4_7) (not p_10_8_7)))
(assert (or (not p_10_4_8) (not p_10_8_8)))
(assert (or (not p_10_4_9) (not p_10_8_9)))
(assert (or (not p_10_4_10) (not p_10_8_10)))
(assert (or (not p_10_4_1) (not p_10_9_1)))
(assert (or (not p_10_4_2) (not p_10_9_2)))
(assert (or (not p_10_4_3) (not p_10_9_3)))
(assert (or (not p_10_4_4) (not p_10_9_4)))
(assert (or (not p_10_4_5) (not p_10_9_5)))
(assert (or (not p_10_4_6) (not p_10_9_6)))
(assert (or (not p_10_4_7) (not p_10_9_7)))
(assert (or (not p_10_4_8) (not p_10_9_8)))
(assert (or (not p_10_4_9) (not p_10_9_9)))
(assert (or (not p_10_4_10) (not p_10_9_10)))
(assert (or (not p_10_4_1) (not p_10_10_1)))
(assert (or (not p_10_4_2) (not p_10_10_2)))
(assert (or (not p_10_4_3) (not p_10_10_3)))
(assert (or (not p_10_4_4) (not p_10_10_4)))
(assert (or (not p_10_4_5) (not p_10_10_5)))
(assert (or (not p_10_4_6) (not p_10_10_6)))
(assert (or (not p_10_4_7) (not p_10_10_7)))
(assert (or (not p_10_4_8) (not p_10_10_8)))
(assert (or (not p_10_4_9) (not p_10_10_9)))
(assert (or (not p_10_4_10) (not p_10_10_10)))
(assert (or (not p_10_5_1) (not p_10_6_1)))
(assert (or (not p_10_5_2) (not p_10_6_2)))
(assert (or (not p_10_5_3) (not p_10_6_3)))
(assert (or (not p_10_5_4) (not p_10_6_4)))
(assert (or (not p_10_5_5) (not p_10_6_5)))
(assert (or (not p_10_5_6) (not p_10_6_6)))
(assert (or (not p_10_5_7) (not p_10_6_7)))
(assert (or (not p_10_5_8) (not p_10_6_8)))
(assert (or (not p_10_5_9) (not p_10_6_9)))
(assert (or (not p_10_5_10) (not p_10_6_10)))
(assert (or (not p_10_5_1) (not p_10_7_1)))
(assert (or (not p_10_5_2) (not p_10_7_2)))
(assert (or (not p_10_5_3) (not p_10_7_3)))
(assert (or (not p_10_5_4) (not p_10_7_4)))
(assert (or (not p_10_5_5) (not p_10_7_5)))
(assert (or (not p_10_5_6) (not p_10_7_6)))
(assert (or (not p_10_5_7) (not p_10_7_7)))
(assert (or (not p_10_5_8) (not p_10_7_8)))
(assert (or (not p_10_5_9) (not p_10_7_9)))
(assert (or (not p_10_5_10) (not p_10_7_10)))
(assert (or (not p_10_5_1) (not p_10_8_1)))
(assert (or (not p_10_5_2) (not p_10_8_2)))
(assert (or (not p_10_5_3) (not p_10_8_3)))
(assert (or (not p_10_5_4) (not p_10_8_4)))
(assert (or (not p_10_5_5) (not p_10_8_5)))
(assert (or (not p_10_5_6) (not p_10_8_6)))
(assert (or (not p_10_5_7) (not p_10_8_7)))
(assert (or (not p_10_5_8) (not p_10_8_8)))
(assert (or (not p_10_5_9) (not p_10_8_9)))
(assert (or (not p_10_5_10) (not p_10_8_10)))
(assert (or (not p_10_5_1) (not p_10_9_1)))
(assert (or (not p_10_5_2) (not p_10_9_2)))
(assert (or (not p_10_5_3) (not p_10_9_3)))
(assert (or (not p_10_5_4) (not p_10_9_4)))
(assert (or (not p_10_5_5) (not p_10_9_5)))
(assert (or (not p_10_5_6) (not p_10_9_6)))
(assert (or (not p_10_5_7) (not p_10_9_7)))
(assert (or (not p_10_5_8) (not p_10_9_8)))
(assert (or (not p_10_5_9) (not p_10_9_9)))
(assert (or (not p_10_5_10) (not p_10_9_10)))
(assert (or (not p_10_5_1) (not p_10_10_1)))
(assert (or (not p_10_5_2) (not p_10_10_2)))
(assert (or (not p_10_5_3) (not p_10_10_3)))
(assert (or (not p_10_5_4) (not p_10_10_4)))
(assert (or (not p_10_5_5) (not p_10_10_5)))
(assert (or (not p_10_5_6) (not p_10_10_6)))
(assert (or (not p_10_5_7) (not p_10_10_7)))
(assert (or (not p_10_5_8) (not p_10_10_8)))
(assert (or (not p_10_5_9) (not p_10_10_9)))
(assert (or (not p_10_5_10) (not p_10_10_10)))
(assert (or (not p_10_6_1) (not p_10_7_1)))
(assert (or (not p_10_6_2) (not p_10_7_2)))
(assert (or (not p_10_6_3) (not p_10_7_3)))
(assert (or (not p_10_6_4) (not p_10_7_4)))
(assert (or (not p_10_6_5) (not p_10_7_5)))
(assert (or (not p_10_6_6) (not p_10_7_6)))
(assert (or (not p_10_6_7) (not p_10_7_7)))
(assert (or (not p_10_6_8) (not p_10_7_8)))
(assert (or (not p_10_6_9) (not p_10_7_9)))
(assert (or (not p_10_6_10) (not p_10_7_10)))
(assert (or (not p_10_6_1) (not p_10_8_1)))
(assert (or (not p_10_6_2) (not p_10_8_2)))
(assert (or (not p_10_6_3) (not p_10_8_3)))
(assert (or (not p_10_6_4) (not p_10_8_4)))
(assert (or (not p_10_6_5) (not p_10_8_5)))
(assert (or (not p_10_6_6) (not p_10_8_6)))
(assert (or (not p_10_6_7) (not p_10_8_7)))
(assert (or (not p_10_6_8) (not p_10_8_8)))
(assert (or (not p_10_6_9) (not p_10_8_9)))
(assert (or (not p_10_6_10) (not p_10_8_10)))
(assert (or (not p_10_6_1) (not p_10_9_1)))
(assert (or (not p_10_6_2) (not p_10_9_2)))
(assert (or (not p_10_6_3) (not p_10_9_3)))
(assert (or (not p_10_6_4) (not p_10_9_4)))
(assert (or (not p_10_6_5) (not p_10_9_5)))
(assert (or (not p_10_6_6) (not p_10_9_6)))
(assert (or (not p_10_6_7) (not p_10_9_7)))
(assert (or (not p_10_6_8) (not p_10_9_8)))
(assert (or (not p_10_6_9) (not p_10_9_9)))
(assert (or (not p_10_6_10) (not p_10_9_10)))
(assert (or (not p_10_6_1) (not p_10_10_1)))
(assert (or (not p_10_6_2) (not p_10_10_2)))
(assert (or (not p_10_6_3) (not p_10_10_3)))
(assert (or (not p_10_6_4) (not p_10_10_4)))
(assert (or (not p_10_6_5) (not p_10_10_5)))
(assert (or (not p_10_6_6) (not p_10_10_6)))
(assert (or (not p_10_6_7) (not p_10_10_7)))
(assert (or (not p_10_6_8) (not p_10_10_8)))
(assert (or (not p_10_6_9) (not p_10_10_9)))
(assert (or (not p_10_6_10) (not p_10_10_10)))
(assert (or (not p_10_7_1) (not p_10_8_1)))
(assert (or (not p_10_7_2) (not p_10_8_2)))
(assert (or (not p_10_7_3) (not p_10_8_3)))
(assert (or (not p_10_7_4) (not p_10_8_4)))
(assert (or (not p_10_7_5) (not p_10_8_5)))
(assert (or (not p_10_7_6) (not p_10_8_6)))
(assert (or (not p_10_7_7) (not p_10_8_7)))
(assert (or (not p_10_7_8) (not p_10_8_8)))
(assert (or (not p_10_7_9) (not p_10_8_9)))
(assert (or (not p_10_7_10) (not p_10_8_10)))
(assert (or (not p_10_7_1) (not p_10_9_1)))
(assert (or (not p_10_7_2) (not p_10_9_2)))
(assert (or (not p_10_7_3) (not p_10_9_3)))
(assert (or (not p_10_7_4) (not p_10_9_4)))
(assert (or (not p_10_7_5) (not p_10_9_5)))
(assert (or (not p_10_7_6) (not p_10_9_6)))
(assert (or (not p_10_7_7) (not p_10_9_7)))
(assert (or (not p_10_7_8) (not p_10_9_8)))
(assert (or (not p_10_7_9) (not p_10_9_9)))
(assert (or (not p_10_7_10) (not p_10_9_10)))
(assert (or (not p_10_7_1) (not p_10_10_1)))
(assert (or (not p_10_7_2) (not p_10_10_2)))
(assert (or (not p_10_7_3) (not p_10_10_3)))
(assert (or (not p_10_7_4) (not p_10_10_4)))
(assert (or (not p_10_7_5) (not p_10_10_5)))
(assert (or (not p_10_7_6) (not p_10_10_6)))
(assert (or (not p_10_7_7) (not p_10_10_7)))
(assert (or (not p_10_7_8) (not p_10_10_8)))
(assert (or (not p_10_7_9) (not p_10_10_9)))
(assert (or (not p_10_7_10) (not p_10_10_10)))
(assert (or (not p_10_8_1) (not p_10_9_1)))
(assert (or (not p_10_8_2) (not p_10_9_2)))
(assert (or (not p_10_8_3) (not p_10_9_3)))
(assert (or (not p_10_8_4) (not p_10_9_4)))
(assert (or (not p_10_8_5) (not p_10_9_5)))
(assert (or (not p_10_8_6) (not p_10_9_6)))
(assert (or (not p_10_8_7) (not p_10_9_7)))
(assert (or (not p_10_8_8) (not p_10_9_8)))
(assert (or (not p_10_8_9) (not p_10_9_9)))
(assert (or (not p_10_8_10) (not p_10_9_10)))
(assert (or (not p_10_8_1) (not p_10_10_1)))
(assert (or (not p_10_8_2) (not p_10_10_2)))
(assert (or (not p_10_8_3) (not p_10_10_3)))
(assert (or (not p_10_8_4) (not p_10_10_4)))
(assert (or (not p_10_8_5) (not p_10_10_5)))
(assert (or (not p_10_8_6) (not p_10_10_6)))
(assert (or (not p_10_8_7) (not p_10_10_7)))
(assert (or (not p_10_8_8) (not p_10_10_8)))
(assert (or (not p_10_8_9) (not p_10_10_9)))
(assert (or (not p_10_8_10) (not p_10_10_10)))
(assert (or (not p_10_9_1) (not p_10_10_1)))
(assert (or (not p_10_9_2) (not p_10_10_2)))
(assert (or (not p_10_9_3) (not p_10_10_3)))
(assert (or (not p_10_9_4) (not p_10_10_4)))
(assert (or (not p_10_9_5) (not p_10_10_5)))
(assert (or (not p_10_9_6) (not p_10_10_6)))
(assert (or (not p_10_9_7) (not p_10_10_7)))
(assert (or (not p_10_9_8) (not p_10_10_8)))
(assert (or (not p_10_9_9) (not p_10_10_9)))
(assert (or (not p_10_9_10) (not p_10_10_10)))
(check-sat)
(get-proof)
