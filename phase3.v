
Load "foo_prot1".

(** * ProtocolPhase3-I : revealing the commitment shcemes *)

(** * Frame [phi16] *)
(** ** term [t14'] *)
 
Definition mphi16 := (conv_mylist_listm (phi15)).
Definition x17 := (f mphi16).
  
Definition kv1vt1 := (if_then_else_M (EQ_M (reveal x17) (V 1))& (EQ_M (to x1) (V 1))   (r 5)
                                       (if_then_else_M (EQ_M (reveal x17) (V 1))& (EQ_M (to x12) (V 1)) (r 17)
                                                       (if_then_else_M (EQ_M (reveal x17) (V 1))& (EQ_M (to x13) (V 1)) (r 25) O))).
Definition kv1vt2 := (if_then_else_M (EQ_M (reveal x17) (V 1))& (EQ_M (to x1) (V 1))   (r 7)
                                       (if_then_else_M (EQ_M (reveal x17) (V 1))& (EQ_M (to x12) (V 1)) (r 19)
                                                       (if_then_else_M (EQ_M (reveal x17) (V 1))& (EQ_M (to x13) (V 1)) (r 27) O))).

Definition kv2vt1 := (if_then_else_M (EQ_M (reveal x17) (V 2))& (EQ_M (to x1) (V 2))   (r 9)
                                       (if_then_else_M (EQ_M (reveal x17) (V 2))& (EQ_M (to x12) (V 2)) (r 13)
                                                       (if_then_else_M (EQ_M (reveal x17) (V 2))& (EQ_M (to x13) (V 2)) (r 21) O))).

Definition kv2vt2 := (if_then_else_M (EQ_M (reveal x17) (V 2))& (EQ_M (to x1) (V 2))   (r 11)
                                       (if_then_else_M (EQ_M (reveal x17) (V 2))& (EQ_M (to x12) (V 2)) (r 15)
                                                       (if_then_else_M (EQ_M (reveal x17) (V 2))& (EQ_M (to x13) (V 2)) (r 23) O))).





Definition qa22_ss := (if_then_else_M (EQ_M (to x15) (V 1))& (EQ_M (dv x15) (vt 1)) kv1vt1
                                   (if_then_else_M (EQ_M (to x15) (V 1))& (EQ_M (dv x15) (vt 2)) kv1vt2
                                                   (if_then_else_M (EQ_M (to x15) (V 2))& (EQ_M (dv x15) (vt 1)) kv2vt1
                                                                   (if_then_else_M (EQ_M (to x15) (V 2))& (EQ_M (dv x15) (vt 2)) kv2vt2
                                                                                   O)))).

(*******************************************************************************)

                                   

Definition qa21_sss :=   (if_then_else_M (EQ_M (to x14) (V 2))&   (bacc (pk 3) (b 0 0 21) (r 22) (pi1 x14)) & (bacc (pk 3) (b 0 1 23) (r 24) (pi2 x14)) qa22_ss O).

Definition qa21'_sss :=   (if_then_else_M (EQ_M (to x14) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x14)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x14)) qa22_ss O).

Definition qa12_sss :=  (if_then_else_M (EQ_M (to x14) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x14)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x14)) qa22_ss O).

Definition qa12'_sss :=  (if_then_else_M (EQ_M (to x14) (V 1))& (bacc (pk 3) (b 0 0 17) (r 18) (pi1 x14)) & (bacc (pk 3) (b 0 1 19) (r 20) (pi2 x14)) qa22_ss O).

Definition qa12''_sss := (if_then_else_M (EQ_M (to x14) (V 1))& (bacc (pk 3) (b 0 0 25) (r 26) (pi1 x14)) & (bacc (pk 3) (b 0 1 27) (r 28) (pi2 x14)) qa22_ss O).

(***************************************************************************)


Definition qa20_ssss := (if_then_else_M (EQ_M (to x13) (V 2)) qa21_sss O).

Definition qa11_ssss :=  (if_then_else_M (EQ_M (to x13) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x13)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x13)) qa21'_sss
			           (if_then_else_M (EQ_M (to x13) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x13)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x13)) qa12_sss O)).

Definition qa11'_ssss :=  (if_then_else_M (EQ_M (to x13) (V 1))& (bacc (pk 3) (b 0 0 17) (r 18) (pi1 x13)) & (bacc (pk 3) (b 0 1 19) (r 20) (pi2 x13)) qa21'_sss
			             (if_then_else_M (EQ_M (to x13) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x13)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x13)) qa12'_sss O)).


Definition qa02_ssss := (if_then_else_M (EQ_M (to x13) (V 1)) qa12''_sss O).

(**************************************************************************)


Definition qa10_sssss := (if_then_else_M (EQ_M (to x12) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x12)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x12)) qa20_ssss 
			          (if_then_else_M (EQ_M (to x12) (V 2)) qa11_ssss O)).
 
Definition qa01_sssss :=  (if_then_else_M (EQ_M (to x12) (V 2))& (bacc (pk 3) (b 0 0 9) (r 10) (pi1 x12)) & (bacc (pk 3) (b 0 1 11) (r 12) (pi2 x12)) qa02_ssss
			           (if_then_else_M (EQ_M (to x12) (V 1)) qa11'_ssss O)).
(*************************************************************************)

Definition t14' :=  (if_then_else_M (EQ_M (to x1) (V 1)) qa10_sssss 
		    	(if_then_else_M (EQ_M (to x1) (V 2))  qa01_sssss  O)).

(** * term [t15'] *)

Definition mphi17 := (conv_mylist_listm (phi15 ++ [msg t14'])).
Definition x18 := (f mphi17).


Definition kv1vt1v2vt1 := (if_then_else_M (EQ_M (reveal x17) (V 1))& (EQ_M (to x1) (V 1))   (r 5)
                                       (if_then_else_M (EQ_M (reveal x17) (V 1))& (EQ_M (to x12) (V 1)) (r 17)
                                                       (if_then_else_M (EQ_M (reveal x17) (V 1))& (EQ_M (to x13) (V 1)) (r 25) (if_then_else_M (EQ_M (reveal x17) (V 2))& (EQ_M (to x1) (V 2))   (r 9)
                                       (if_then_else_M (EQ_M (reveal x17) (V 2))& (EQ_M (to x12) (V 2)) (r 13)

                                                       (if_then_else_M (EQ_M (reveal x17) (V 2))& (EQ_M (to x13) (V 2)) (r 21) O)))))).
Definition kv1vt1v2vt2:= 
(if_then_else_M (EQ_M (reveal x17) (V 1))& (EQ_M (to x1) (V 1))   (r 5)

                (if_then_else_M (EQ_M (reveal x17) (V 1))& (EQ_M (to x12) (V 1)) (r 17)

                                (if_then_else_M (EQ_M (reveal x17) (V 1))& (EQ_M (to x13) (V 1)) (r 25)
(if_then_else_M (EQ_M (reveal x17) (V 2))& (EQ_M (to x1) (V 2))   (r 11)
                                       (if_then_else_M (EQ_M (reveal x17) (V 2))& (EQ_M (to x12) (V 2)) (r 15)
                                                       (if_then_else_M (EQ_M (reveal x17) (V 2))& (EQ_M (to x13) (V 2)) (r 23) O)))))).
Definition kv1vt2v2vt2 :=

 (if_then_else_M (EQ_M (reveal x17) (V 1))& (EQ_M (to x1) (V 1))   (r 7)
                                       (if_then_else_M (EQ_M (reveal x17) (V 1))& (EQ_M (to x12) (V 1)) (r 19)
                                                       (if_then_else_M (EQ_M (reveal x17) (V 1))& (EQ_M (to x13) (V 1)) (r 27)
 (if_then_else_M (EQ_M (reveal x17) (V 2))& (EQ_M (to x1) (V 2))   (r 11)
                                       (if_then_else_M (EQ_M (reveal x17) (V 2))& (EQ_M (to x12) (V 2)) (r 15)
                                                       (if_then_else_M (EQ_M (reveal x17) (V 2))& (EQ_M (to x13) (V 2)) (r 23) O)))))).



Definition qa23_s :=    (if_then_else_M (EQ_M (to x16) (V 2))& (EQ_M (dv x16) (vt 1)) kv1vt1v2vt1
                                                   (if_then_else_M (EQ_M (to x16) (V 2))& (EQ_M (dv x16) (vt 2)) kv1vt1v2vt2
                                                                   O)).
Definition qa33_s :=  (if_then_else_M (EQ_M (to x16) (V 1))& (EQ_M (dv x16) (vt 1)) kv1vt1v2vt1
                                                   (if_then_else_M (EQ_M (to x16) (V 1))& (EQ_M (dv x16) (vt 2)) kv1vt2v2vt2
                                                                   O)).

Definition qa22_s' := (if_then_else_M (EQ_M (to x15) (V 1))& (EQ_M (dv x15) (vt 1)) qa23_s
                                   (if_then_else_M (EQ_M (to x15) (V 1))& (EQ_M (dv x15) (vt 2)) qa23_s
                                                   (if_then_else_M (EQ_M (to x15) (V 2))& (EQ_M (dv x15) (vt 1)) qa33_s
                                                                   (if_then_else_M (EQ_M (to x15) (V 2))& (EQ_M (dv x15) (vt 2)) qa33_s
                                                                                   O)))).

(*******************************************************************************)

                                   

Definition qa21_sss' :=   (if_then_else_M (EQ_M (to x14) (V 2))&   (bacc (pk 3) (b 0 0 21) (r 22) (pi1 x14)) & (bacc (pk 3) (b 0 1 23) (r 24) (pi2 x14)) qa22_s' O).

Definition qa21'_sss' :=   (if_then_else_M (EQ_M (to x14) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x14)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x14)) qa22_s' O).

Definition qa12_sss' :=  (if_then_else_M (EQ_M (to x14) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x14)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x14)) qa22_s' O).

Definition qa12'_sss' :=  (if_then_else_M (EQ_M (to x14) (V 1))& (bacc (pk 3) (b 0 0 17) (r 18) (pi1 x14)) & (bacc (pk 3) (b 0 1 19) (r 20) (pi2 x14)) qa22_s' O).

Definition qa12''_sss' := (if_then_else_M (EQ_M (to x14) (V 1))& (bacc (pk 3) (b 0 0 25) (r 26) (pi1 x14)) & (bacc (pk 3) (b 0 1 27) (r 28) (pi2 x14)) qa22_s' O).

(***************************************************************************)


Definition qa20_ssss' := (if_then_else_M (EQ_M (to x13) (V 2)) qa21_sss' O).

Definition qa11_ssss' :=  (if_then_else_M (EQ_M (to x13) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x13)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x13)) qa21'_sss'
			           (if_then_else_M (EQ_M (to x13) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x13)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x13)) qa12_sss' O)).

Definition qa11'_ssss' :=  (if_then_else_M (EQ_M (to x13) (V 1))& (bacc (pk 3) (b 0 0 17) (r 18) (pi1 x13)) & (bacc (pk 3) (b 0 1 19) (r 20) (pi2 x13)) qa21'_sss'
			             (if_then_else_M (EQ_M (to x13) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x13)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x13)) qa12'_sss' O)).


Definition qa02_ssss' := (if_then_else_M (EQ_M (to x13) (V 1)) qa12''_sss' O).

(**************************************************************************)


Definition qa10_sssss' := (if_then_else_M (EQ_M (to x12) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x12)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x12)) qa20_ssss' 
			          (if_then_else_M (EQ_M (to x12) (V 2)) qa11_ssss' O)).
 
Definition qa01_sssss' :=  (if_then_else_M (EQ_M (to x12) (V 2))& (bacc (pk 3) (b 0 0 9) (r 10) (pi1 x12)) & (bacc (pk 3) (b 0 1 11) (r 12) (pi2 x12)) qa02_ssss'
			           (if_then_else_M (EQ_M (to x12) (V 1)) qa11'_ssss' O)).
(*************************************************************************)

Definition t15' :=  (if_then_else_M (EQ_M (to x1) (V 1)) qa10_sssss'
		    	(if_then_else_M (EQ_M (to x1) (V 2))  qa01_sssss'  O)).
 

(** * Shuffle the keys, i.e., output the keys in lexicographic order *)


Definition pa22' := (shuf (dec (chksign (sk 5) t14') (sk 5)) (dec (chksign (sk 5) t15') (sk 5))).

(*******************************************************************************)

                                   

Definition pa21_s' :=   (if_then_else_M (EQ_M (to x14) (V 2))&   (bacc (pk 3) (b 0 0 21) (r 22) (pi1 x14)) & (bacc (pk 3) (b 0 1 23) (r 24) (pi2 x14)) pa22' O).

Definition pa21'_s' :=   (if_then_else_M (EQ_M (to x14) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x14)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x14)) pa22' O).

Definition pa12_s' :=  (if_then_else_M (EQ_M (to x14) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x14)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x14)) pa22' O).

Definition pa12'_s' :=  (if_then_else_M (EQ_M (to x14) (V 1))& (bacc (pk 3) (b 0 0 17) (r 18) (pi1 x14)) & (bacc (pk 3) (b 0 1 19) (r 20) (pi2 x14)) pa22' O).

Definition pa12''_s' := (if_then_else_M (EQ_M (to x14) (V 1))& (bacc (pk 3) (b 0 0 25) (r 26) (pi1 x14)) & (bacc (pk 3) (b 0 1 27) (r 28) (pi2 x14)) pa22' O).

(***************************************************************************)


Definition pa20_ss' := (if_then_else_M (EQ_M (to x13) (V 2)) pa21_s' O).

Definition pa11_ss' :=  (if_then_else_M (EQ_M (to x13) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x13)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x13)) pa21'_s'
			           (if_then_else_M (EQ_M (to x13) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x13)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x13)) pa12_s' O)).

Definition pa11'_ss' :=  (if_then_else_M (EQ_M (to x13) (V 1))& (bacc (pk 3) (b 0 0 17) (r 18) (pi1 x13)) & (bacc (pk 3) (b 0 1 19) (r 20) (pi2 x13)) pa21'_s'
			             (if_then_else_M (EQ_M (to x13) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x13)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x13)) pa12'_s' O)).


Definition pa02_ss' := (if_then_else_M (EQ_M (to x13) (V 1)) pa12''_s' O).

(**************************************************************************)


Definition pa10_sss' := (if_then_else_M (EQ_M (to x12) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x12)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x12)) pa20_ss' 
			          (if_then_else_M (EQ_M (to x12) (V 2)) pa11_ss' O)).
 
Definition pa01_sss' :=  (if_then_else_M (EQ_M (to x12) (V 2))& (bacc (pk 3) (b 0 0 9) (r 10) (pi1 x12)) & (bacc (pk 3) (b 0 1 11) (r 12) (pi2 x12)) pa02_ss'
			           (if_then_else_M (EQ_M (to x12) (V 1)) pa11'_ss' O)).
(*************************************************************************)

Definition t16' :=  (if_then_else_M (EQ_M (to x1) (V 1)) pa10_sss' 
		    	            (if_then_else_M (EQ_M (to x1) (V 2))  pa01_sss'  O)).

Definition phi16 := phi15 ++ [msg t16'].


(** ProtocolPhase3-II: revealing commitment schemes *)


(** ** term [t24] *)
 
Definition qb22_ss := (if_then_else_M (EQ_M (to x15) (V 1))& (EQ_M (dv x15) (vt 1)) (chksign (pk 1) (sign (sk 1) (enc (pi2 x15) (pk 5) (r 29))))
                                   (if_then_else_M (EQ_M (to x15) (V 1))& (EQ_M (dv x15) (vt 2)) (chksign (pk 1) (sign (sk 1) (enc (pi1 x15) (pk 5) (r 30))))
                                                   (if_then_else_M (EQ_M (to x15) (V 2))& (EQ_M (dv x15) (vt 1)) (chksign (pk 2) (sign (sk 2) (enc (pi2 x15) (pk 5) (r 31))))
                                                                   (if_then_else_M (EQ_M (to x15) (V 2))& (EQ_M (dv x15) (vt 2)) (chksign (pk 2) (sign (sk 2) (enc (pi1 x15) (pk 5) (r 32))))
                                                                                   O)))).

(***************************************************************************)

                                   

Definition qb21_s :=   (if_then_else_M (EQ_M (to x14) (V 2))&   (bacc (pk 3) (b 0 0 21) (r 22) (pi1 x14)) & (bacc (pk 3) (b 0 1 23) (r 24) (pi2 x14)) qb22 O).

Definition qb21'_s :=   (if_then_else_M (EQ_M (to x14) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x14)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x14)) qb22 O).

Definition qb12_s :=  (if_then_else_M (EQ_M (to x14) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x14)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x14)) qb22 O).

Definition qb12'_s :=  (if_then_else_M (EQ_M (to x14) (V 1))& (bacc (pk 3) (b 0 0 17) (r 18) (pi1 x14)) & (bacc (pk 3) (b 0 1 19) (r 20) (pi2 x14)) qb22 O).

Definition qb12''_s := (if_then_else_M (EQ_M (to x14) (V 1))& (bacc (pk 3) (b 0 0 25) (r 26) (pi1 x14)) & (bacc (pk 3) (b 0 1 27) (r 28) (pi2 x14)) qb22 O).

(***************************************************************************)


Definition qb20_ss := (if_then_else_M (EQ_M (to x13) (V 2)) qb21_s O).

Definition qb11_ss :=  (if_then_else_M (EQ_M (to x13) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x13)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x13)) qb21'_s
			           (if_then_else_M (EQ_M (to x13) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x13)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x13)) qb12_s O)).

Definition qb11'_ss :=  (if_then_else_M (EQ_M (to x13) (V 1))& (bacc (pk 3) (b 0 0 17) (r 18) (pi1 x13)) & (bacc (pk 3) (b 0 1 19) (r 20) (pi2 x13)) qb21'_s
			             (if_then_else_M (EQ_M (to x13) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x13)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x13)) qb12'_s O)).


Definition qb02_ss := (if_then_else_M (EQ_M (to x13) (V 1)) qb12''_s O).

(**************************************************************************)


Definition qb10_sss := (if_then_else_M (EQ_M (to x12) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x12)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x12)) qb20_ss 
			          (if_then_else_M (EQ_M (to x12) (V 2)) qb11_ss O)).
 
Definition qb01_sss :=  (if_then_else_M (EQ_M (to x12) (V 2))& (bacc (pk 3) (b 0 0 9) (r 10) (pi1 x12)) & (bacc (pk 3) (b 0 1 11) (r 12) (pi2 x12)) qb02_ss
			           (if_then_else_M (EQ_M (to x12) (V 1)) qb11'_ss O)).
(*************************************************************************)

Definition t24 :=  (if_then_else_M (EQ_M (to x1) (V 1)) qb10_sss 
		    	(if_then_else_M (EQ_M (to x1) (V 2))  qb01_sss  O)).


(** ** term [t25] *)
 
 
Definition mphi25 := (conv_mylist_listm (phi14 ++ [msg t24])).
Definition x26 := (f mphi25).
 
Definition qb23 :=    (if_then_else_M (EQ_M (to x26) (V 2))& (EQ_M (dv x26) (vt 1)) (chksign (pk 2) (sign (sk 2) (enc (pi2 x26) (pk 5) (r 33))))
                                                   (if_then_else_M (EQ_M (to x26) (V 2))& (EQ_M (dv x26) (vt 2)) (chksign (pk 2) (sign (sk 2) (enc (pi1 x26) (pk 5) (r 34))))
                                                                   O)).
Definition qb33 :=  (if_then_else_M (EQ_M (to x26) (V 1))& (EQ_M (dv x26) (vt 1)) (chksign (pk 1) (sign (sk 1) (enc (pi2 x26) (pk 5) (r 35))))
                                                   (if_then_else_M (EQ_M (to x26) (V 1))& (EQ_M (dv x26) (vt 2)) (chksign (pk 1) (sign (sk 1) (enc (pi1 x26) (pk 5) (r 36))))
                                                                   O)).

Definition qb22_s := (if_then_else_M (EQ_M (to x15) (V 1))& (EQ_M (dv x15) (vt 1)) qb23
                                   (if_then_else_M (EQ_M (to x15) (V 1))& (EQ_M (dv x15) (vt 2)) qb23
                                                   (if_then_else_M (EQ_M (to x15) (V 2))& (EQ_M (dv x15) (vt 1)) qb33
                                                                   (if_then_else_M (EQ_M (to x15) (V 2))& (EQ_M (dv x15) (vt 2)) qb33
                                                                                   O)))).

(*******************************************************************************)

                                   

Definition qb21_ss :=   (if_then_else_M (EQ_M (to x14) (V 2))&   (bacc (pk 3) (b 0 0 21) (r 22) (pi1 x14)) & (bacc (pk 3) (b 0 1 23) (r 24) (pi2 x14)) qb22_s O).

Definition qb21'_ss :=   (if_then_else_M (EQ_M (to x14) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x14)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x14)) qb22_s O).

Definition qb12_ss :=  (if_then_else_M (EQ_M (to x14) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x14)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x14)) qb22_s O).

Definition qb12'_ss :=  (if_then_else_M (EQ_M (to x14) (V 1))& (bacc (pk 3) (b 0 0 17) (r 18) (pi1 x14)) & (bacc (pk 3) (b 0 1 19) (r 20) (pi2 x14)) qb22_s O).

Definition qb12''_ss := (if_then_else_M (EQ_M (to x14) (V 1))& (bacc (pk 3) (b 0 0 25) (r 26) (pi1 x14)) & (bacc (pk 3) (b 0 1 27) (r 28) (pi2 x14)) qb22_s O).

(***************************************************************************)


Definition qb20_sss := (if_then_else_M (EQ_M (to x13) (V 2)) qb21_ss O).

Definition qb11_sss :=  (if_then_else_M (EQ_M (to x13) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x13)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x13)) qb21'_ss
			           (if_then_else_M (EQ_M (to x13) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x13)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x13)) qb12_ss O)).

Definition qb11'_sss :=  (if_then_else_M (EQ_M (to x13) (V 1))& (bacc (pk 3) (b 0 0 17) (r 18) (pi1 x13)) & (bacc (pk 3) (b 0 1 19) (r 20) (pi2 x13)) qb21'_ss
			             (if_then_else_M (EQ_M (to x13) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x13)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x13)) qb12'_ss O)).


Definition qb02_sss := (if_then_else_M (EQ_M (to x13) (V 1)) qb12''_ss O).

(**************************************************************************)


Definition qb10_ssss := (if_then_else_M (EQ_M (to x12) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x12)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x12)) qb20_sss 
			          (if_then_else_M (EQ_M (to x12) (V 2)) qb11_sss O)).
 
Definition qb01_ssss :=  (if_then_else_M (EQ_M (to x12) (V 2))& (bacc (pk 3) (b 0 0 9) (r 10) (pi1 x12)) & (bacc (pk 3) (b 0 1 11) (r 12) (pi2 x12)) qb02_sss
			           (if_then_else_M (EQ_M (to x12) (V 1)) qb11'_sss O)).
(*************************************************************************)

Definition t25 :=  (if_then_else_M (EQ_M (to x1) (V 1)) qb10_ssss
		    	(if_then_else_M (EQ_M (to x1) (V 2))  qb01_ssss  O)).


(** ** Shuffle: performs lexicographic ordering terms *)


Definition pb22 := (shuf (dec  qb22 (sk 5)) (dec  qb22_s (sk 5))).

(*******************************************************************************)

                                   

Definition pb21_s :=   (if_then_else_M (EQ_M (to x14) (V 2))&   (bacc (pk 3) (b 0 0 21) (r 22) (pi1 x14)) & (bacc (pk 3) (b 0 1 23) (r 24) (pi2 x14)) pb22 O).

Definition pb21'_s :=   (if_then_else_M (EQ_M (to x14) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x14)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x14)) pb22 O).

Definition pb12_s :=  (if_then_else_M (EQ_M (to x14) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x14)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x14)) pb22 O).

Definition pb12'_s :=  (if_then_else_M (EQ_M (to x14) (V 1))& (bacc (pk 3) (b 0 0 17) (r 18) (pi1 x14)) & (bacc (pk 3) (b 0 1 19) (r 20) (pi2 x14)) pb22 O).

Definition pb12''_s := (if_then_else_M (EQ_M (to x14) (V 1))& (bacc (pk 3) (b 0 0 25) (r 26) (pi1 x14)) & (bacc (pk 3) (b 0 1 27) (r 28) (pi2 x14)) pb22 O).

(***************************************************************************)


Definition pb20_ss := (if_then_else_M (EQ_M (to x13) (V 2)) pb21_s O).

Definition pb11_ss :=  (if_then_else_M (EQ_M (to x13) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x13)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x13)) pb21'_s
			           (if_then_else_M (EQ_M (to x13) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x13)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x13)) pb12_s O)).

Definition pb11'_ss :=  (if_then_else_M (EQ_M (to x13) (V 1))& (bacc (pk 3) (b 0 0 17) (r 18) (pi1 x13)) & (bacc (pk 3) (b 0 1 19) (r 20) (pi2 x13)) pb21'_s
			             (if_then_else_M (EQ_M (to x13) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x13)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x13)) pb12'_s O)).


Definition pb02_ss := (if_then_else_M (EQ_M (to x13) (V 1)) pb12''_s O).

(**************************************************************************)


Definition pb10_sss := (if_then_else_M (EQ_M (to x12) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x12)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x12)) pb20_ss 
			          (if_then_else_M (EQ_M (to x12) (V 2)) pb11_ss O)).
 
Definition pb01_sss :=  (if_then_else_M (EQ_M (to x12) (V 2))& (bacc (pk 3) (b 0 0 9) (r 10) (pi1 x12)) & (bacc (pk 3) (b 0 1 11) (r 12) (pi2 x12)) pb02_ss
			           (if_then_else_M (EQ_M (to x12) (V 1)) pb11'_ss O)).
(*************************************************************************)

Definition t26 :=  (if_then_else_M (EQ_M (to x1) (V 1)) pb10_sss 
		    	(if_then_else_M (EQ_M (to x1) (V 2))  pb01_sss  O)).
Definition phi25 := phi14 ++ [msg t26].


