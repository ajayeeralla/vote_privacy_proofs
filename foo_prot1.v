Load "tactics".  
 
 
(** * FOO Voting Prtocol *)
(** ** Phase-I *)
(** 
- V -> A : (V, sign(blind(commit(v, r), r'), sk(V)))

- A-> V :  sign(blind(commit(v, r), r'), sk(A)) *)

Section foo_prot1.   

(** - We assume that adminisrator and collector are dishonest 
    - Hence, random numbers used to generate keys (pair) of them included in attacker's knowledge *)

(** * ProtocolPhase-I: There are two voters [V1] and [V2], and their corresponding votes [va] and [vb] respectively. *)
 
(** * Frame [phi0]: initial knowledge *)
(** 1-Voter1, 2-Voter2, 3-Administrator, 4-Collector, 5-Mixnet 
[(pk 0)] represents a public key used in commitment shceme. *) 

  
Definition vt (n:nat) := (v (N n)).
Definition phi0:= [msg (pk 0); msg (pk 1); msg (pk 2);  msg (N 3); msg (N 4); msg (pk 5)].

(** * Frame [phi11] *)

(** commitments *) 

Definition b (n n' n'':nat) := (commit (pk n) (v (N n')) (r n'')).
Definition e (n :nat) (t:message) (n':nat) := (blind t (pk n) (r n')).


(** Converting [mylist] to [list message] *)
 

Definition mphi0 := (conv_mylist_listm phi0).

(** attacker's computation *)

Definition x1 := (f mphi0).  
   
(** next step *)    

Definition qa00 :=  (if_then_else_M (EQ_M (to x1) (V 1)) ((pk 1), ((sign (sk 1) (e 3 (b 0 0 5) 6)) , (sign (sk 1) (e 3 (b 0 1 7) 8 ))))
		    	            (if_then_else_M (EQ_M (to x1) (V 2)) ((pk 2), ((sign (sk 2) (e 3 (b 0 0 9) 10)) , (sign (sk 2) (e 3 (b 0 1 11) 12 )))) O)).


(** attacker's knowledge *)

Definition phi11 := phi0 ++ [msg qa00].


(** * Frame [phi12] *)

Definition mphi11 := (conv_mylist_listm phi11).
Definition x12 := (f mphi11).  
 
Definition qa10:= (if_then_else_M (EQ_M (to x12) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x12)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x12)) ok 
			          (if_then_else_M (EQ_M (to x12) (V 2)) ((pk 2), ((sign (sk 2) (e 3 (b 0 0 13) 14)) , (sign (sk 2) (e 3 (b 0 1 15) 16)))) O)).
 
Definition qa01:=  (if_then_else_M (EQ_M (to x12) (V 2))& (bacc (pk 3) (b 0 0 9) (r 10) (pi1 x12)) & (bacc (pk 3) (b 0 1 11) (r 12) (pi2 x12)) ok 
			           (if_then_else_M (EQ_M (to x12) (V 1)) ((pk 1), ((sign (sk 1) (e 3 (b 0 0 17) 18)) , (sign (sk 1) (e 3 (b 0 1 19) 20 ))))
                                                   O)).

Definition t11 :=  (if_then_else_M (EQ_M (to x1) (V 1)) qa10 
		    	(if_then_else_M (EQ_M (to x1) (V 2))  qa01  O)).

Definition phi12 := phi11 ++ [msg t11].


(** * Frame [phi13] *)

Definition mphi12 := (conv_mylist_listm phi12).
Definition x13 := (f mphi12).

Definition qa20 := (if_then_else_M (EQ_M (to x13) (V 2)) ((pk 2), ((sign (sk 2) (e 3 (b 0 0 21) 22)) , (sign (sk 2) (e 3 (b 0 1 23) 24))))
                                   O).

Definition qa11 :=  (if_then_else_M (EQ_M (to x13) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x13)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x13)) ok
			           (if_then_else_M (EQ_M (to x13) (V 2))& (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x13)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x13)) ok O)).

Definition qa11' :=  (if_then_else_M (EQ_M (to x13) (V 1))& (bacc (pk 3) (b 0 0 17) (r 18) (pi1 x13)) & (bacc (pk 3) (b 0 1 19) (r 20) (pi2 x13)) ok
			             (if_then_else_M (EQ_M (to x13) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x13)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x13)) ok O)).


Definition qa02 := (if_then_else_M (EQ_M (to x13) (V 1)) ((pk 1), ((sign (sk 1) (e 3 (b 0 0 25) 26)) , (sign (sk 1) (e 3 (b 0 1 27) 28 )))) O).

(**************************************************************************)


Definition qa10_s := (if_then_else_M (EQ_M (to x12) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x12)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x12)) qa20 
			          (if_then_else_M (EQ_M (to x12) (V 2)) qa11 O)).
 
Definition qa01_s :=  (if_then_else_M (EQ_M (to x12) (V 2))& (bacc (pk 3) (b 0 0 9) (r 10) (pi1 x12)) & (bacc (pk 3) (b 0 1 11) (r 12) (pi2 x12)) qa02
			           (if_then_else_M (EQ_M (to x12) (V 1)) qa11'
                                                   O)).


Definition t12 :=  (if_then_else_M (EQ_M (to x1) (V 1)) qa10_s 
		    	(if_then_else_M (EQ_M (to x1) (V 2))  qa01_s  O)).

Definition phi13 := phi12 ++ [msg t12].


(** * Frame [phi14] *)
 
Definition mphi13 := (conv_mylist_listm phi13).
Definition x14 := (f mphi13).

Definition qa21 :=   (if_then_else_M (EQ_M (to x14) (V 2))&   (bacc (pk 3) (b 0 0 21) (r 22) (pi1 x14)) & (bacc (pk 3) (b 0 1 23) (r 24) (pi2 x14)) ok O).

Definition qa21' :=   (if_then_else_M (EQ_M (to x14) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x14)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x14)) ok O).

Definition qa12 :=  (if_then_else_M (EQ_M (to x14) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x14)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x14)) ok O).

Definition qa12' :=  (if_then_else_M (EQ_M (to x14) (V 1))& (bacc (pk 3) (b 0 0 17) (r 18) (pi1 x14)) & (bacc (pk 3) (b 0 1 19) (r 20) (pi2 x14)) ok O).

Definition qa12'' := (if_then_else_M (EQ_M (to x14) (V 1))& (bacc (pk 3) (b 0 0 25) (r 26) (pi1 x14)) & (bacc (pk 3) (b 0 1 27) (r 28) (pi2 x14)) ok O).

(***************************************************************************)


Definition qa20_s := (if_then_else_M (EQ_M (to x13) (V 2)) qa21 O).

Definition qa11_s :=  (if_then_else_M (EQ_M (to x13) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x13)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x13)) qa21'
			           (if_then_else_M (EQ_M (to x13) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x13)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x13)) qa12 O)).

Definition qa11'_s :=  (if_then_else_M (EQ_M (to x13) (V 1))& (bacc (pk 3) (b 0 0 17) (r 18) (pi1 x13)) & (bacc (pk 3) (b 0 1 19) (r 20) (pi2 x13)) qa21'
			             (if_then_else_M (EQ_M (to x13) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x13)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x13)) qa12' O)).


Definition qa02_s := (if_then_else_M (EQ_M (to x13) (V 1)) qa12'' O).

(**************************************************************************)


Definition qa10_ss := (if_then_else_M (EQ_M (to x12) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x12)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x12)) qa20_s 
			          (if_then_else_M (EQ_M (to x12) (V 2)) qa11_s O)).
 
Definition qa01_ss :=  (if_then_else_M (EQ_M (to x12) (V 2))& (bacc (pk 3) (b 0 0 9) (r 10) (pi1 x12)) & (bacc (pk 3) (b 0 1 11) (r 12) (pi2 x12)) qa02_s
			           (if_then_else_M (EQ_M (to x12) (V 1)) qa11'_s O)).
(*************************************************************************)

Definition t13 :=  (if_then_else_M (EQ_M (to x1) (V 1)) qa10_ss 
		    	(if_then_else_M (EQ_M (to x1) (V 2))  qa01_ss  O)).

Definition phi14 := phi13 ++ [msg t13].

(** * ProtocolPhase1-II: In phase1, it is same as the ProtocolPhase1-I *)

Definition phi24 := phi14.

(** * Phase1 Proof: The frames exactly same in the protocols *)

Theorem Phase1Ind : phi14~phi24.

Proof. reflexivity. Qed.



(** * ProtocolPhase2-I:  *) 

(** * Frame [phi15] *)

(** ** term [t14] *)

Definition mphi14 := (conv_mylist_listm phi14).
Definition x15 := (f mphi14).
 
Definition ubv0 n1 n2 t := (unblind (pk 3) (b 0 0 n1) (r n2)  (pi1 t)).
Definition ubv1 n1 n2 t := (unblind (pk 3) (b 0 1 n1) (r n2)  (pi2 t)).

    
 
Definition qa221 := (if_then_else_M (EQ_M (to x15) (V 1))  ((enc (ubv0 5 6 x12) (pk 5) (r 29)), (sign (sk 1) (enc (ubv0 5 6 x12) (pk 5) (r 29))))
                                    (if_then_else_M (EQ_M (to x15) (V 2))  ((enc (ubv1 23 24 x14) (pk 5) (r 30)) , (sign (sk 1) (enc (ubv1 23 24 x14) (pk 5) (r 30)))) O)).


Definition qa222 := (if_then_else_M (EQ_M (to x15) (V 1))  ((enc (ubv0 5 6 x13) (pk 5) (r 31)), (sign (sk 1) (enc (ubv0 5 6 x13) (pk 5) (r 31))))
                                    (if_then_else_M (EQ_M (to x15) (V 2))  ((enc (pi2 x14) (pk 5) (r 29)), (sign (sk 1) (enc (pi2 x14) (pk 5) (r 29)))) O)).

Definition qa223 := (if_then_else_M (EQ_M (to x15) (V 1))  ((enc (pi1 x14) (pk 5) (r 29)), (sign (sk 1) (enc (pi1 x14) (pk 5) (r 29))))
                                    (if_then_else_M (EQ_M (to x15) (V 2))  ((enc (pi2 x13) (pk 5) (r 29)), (sign (sk 1) (enc (pi2 x13) (pk 5) (r 29)))) O)).

Definition qa224 := (if_then_else_M (EQ_M (to x15) (V 1))  ((enc (pi1 x14) (pk 5) (r 29)), (sign (sk 1) (enc (pi1 x14) (pk 5) (r 29))))
                                    (if_then_else_M (EQ_M (to x15) (V 2))  ((enc (pi2 x13) (pk 5) (r 29)), (sign (sk 1) (enc (pi2 x13) (pk 5) (r 29)))) O)).

Definition qa225 := (if_then_else_M (EQ_M (to x15) (V 1))  ((enc (pi1 x14) (pk 5) (r 29)), (sign (sk 1) (enc (pi1 x14) (pk 5) (r 29))))
                                   (if_then_else_M (EQ_M (to x15) (V 2))  ((enc (pi2 x12) (pk 5) (r 29)), (sign (sk 1) (enc (pi2 x12) (pk 5) (r 29)))) O)).

(***************************************************************************)

                                   

Definition qa21_s :=   (if_then_else_M (EQ_M (to x14) (V 2))&   (bacc (pk 3) (b 0 0 21) (r 22) (pi1 x14)) & (bacc (pk 3) (b 0 1 23) (r 24) (pi2 x14)) qa22 O).

Definition qa21'_s :=   (if_then_else_M (EQ_M (to x14) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x14)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x14)) qa22 O).

Definition qa12_s :=  (if_then_else_M (EQ_M (to x14) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x14)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x14)) qa22 O).

Definition qa12'_s :=  (if_then_else_M (EQ_M (to x14) (V 1))& (bacc (pk 3) (b 0 0 17) (r 18) (pi1 x14)) & (bacc (pk 3) (b 0 1 19) (r 20) (pi2 x14)) qa22 O).

Definition qa12''_s := (if_then_else_M (EQ_M (to x14) (V 1))& (bacc (pk 3) (b 0 0 25) (r 26) (pi1 x14)) & (bacc (pk 3) (b 0 1 27) (r 28) (pi2 x14)) qa22 O).

(***************************************************************************)


Definition qa20_ss := (if_then_else_M (EQ_M (to x13) (V 2)) qa21_s O).

Definition qa11_ss :=  (if_then_else_M (EQ_M (to x13) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x13)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x13)) qa21'_s
			           (if_then_else_M (EQ_M (to x13) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x13)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x13)) qa12_s O)).

Definition qa11'_ss :=  (if_then_else_M (EQ_M (to x13) (V 1))& (bacc (pk 3) (b 0 0 17) (r 18) (pi1 x13)) & (bacc (pk 3) (b 0 1 19) (r 20) (pi2 x13)) qa21'_s
			             (if_then_else_M (EQ_M (to x13) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x13)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x13)) qa12'_s O)).


Definition qa02_ss := (if_then_else_M (EQ_M (to x13) (V 1)) qa12''_s O).

(**************************************************************************)


Definition qa10_sss := (if_then_else_M (EQ_M (to x12) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x12)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x12)) qa20_ss 
			          (if_then_else_M (EQ_M (to x12) (V 2)) qa11_ss O)).
 
Definition qa01_sss :=  (if_then_else_M (EQ_M (to x12) (V 2))& (bacc (pk 3) (b 0 0 9) (r 10) (pi1 x12)) & (bacc (pk 3) (b 0 1 11) (r 12) (pi2 x12)) qa02_ss
			           (if_then_else_M (EQ_M (to x12) (V 1)) qa11'_ss O)).
(*************************************************************************)

Definition t14 :=  (if_then_else_M (EQ_M (to x1) (V 1)) qa10_sss 
		    	(if_then_else_M (EQ_M (to x1) (V 2))  qa01_sss  O)).


(** ** term [t15] *)
 
 
Definition mphi15 := (conv_mylist_listm (phi14 ++ [msg t14])).
Definition x16 := (f mphi15).
 
Definition qa23 :=    (if_then_else_M (EQ_M (to x16) (V 2))& (EQ_M (dv x16) (vt 1)) (chksign (pk 2) (sign (sk 2) (enc (pi1 x16) (pk 5) (r 33))))
                                                   (if_then_else_M (EQ_M (to x16) (V 2))& (EQ_M (dv x16) (vt 2)) (chksign (pk 2) (sign (sk 2) (enc (pi2 x16) (pk 5) (r 34))))
                                                                   O)).
Definition qa33 :=  (if_then_else_M (EQ_M (to x16) (V 1))& (EQ_M (dv x16) (vt 1)) (chksign (pk 1) (sign (sk 1) (enc (pi1 x16) (pk 5) (r 35))))
                                                   (if_then_else_M (EQ_M (to x16) (V 1))& (EQ_M (dv x16) (vt 2)) (chksign (pk 1) (sign (sk 1) (enc (pi2 x16) (pk 5) (r 36))))
                                                                   O)).

Definition qa22_s := (if_then_else_M (EQ_M (to x15) (V 1))& (EQ_M (dv x15) (vt 1)) qa23
                                   (if_then_else_M (EQ_M (to x15) (V 1))& (EQ_M (dv x15) (vt 2)) qa23
                                                   (if_then_else_M (EQ_M (to x15) (V 2))& (EQ_M (dv x15) (vt 1)) qa33
                                                                   (if_then_else_M (EQ_M (to x15) (V 2))& (EQ_M (dv x15) (vt 2)) qa33
                                                                                   O)))).

(*******************************************************************************)

                                   

Definition qa21_ss :=   (if_then_else_M (EQ_M (to x14) (V 2))&   (bacc (pk 3) (b 0 0 21) (r 22) (pi1 x14)) & (bacc (pk 3) (b 0 1 23) (r 24) (pi2 x14)) qa22_s O).

Definition qa21'_ss :=   (if_then_else_M (EQ_M (to x14) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x14)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x14)) qa22_s O).

Definition qa12_ss :=  (if_then_else_M (EQ_M (to x14) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x14)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x14)) qa22_s O).

Definition qa12'_ss :=  (if_then_else_M (EQ_M (to x14) (V 1))& (bacc (pk 3) (b 0 0 17) (r 18) (pi1 x14)) & (bacc (pk 3) (b 0 1 19) (r 20) (pi2 x14)) qa22_s O).

Definition qa12''_ss := (if_then_else_M (EQ_M (to x14) (V 1))& (bacc (pk 3) (b 0 0 25) (r 26) (pi1 x14)) & (bacc (pk 3) (b 0 1 27) (r 28) (pi2 x14)) qa22_s O).

(***************************************************************************)


Definition qa20_sss := (if_then_else_M (EQ_M (to x13) (V 2)) qa21_ss O).

Definition qa11_sss :=  (if_then_else_M (EQ_M (to x13) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x13)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x13)) qa21'_ss
			           (if_then_else_M (EQ_M (to x13) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x13)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x13)) qa12_ss O)).

Definition qa11'_sss :=  (if_then_else_M (EQ_M (to x13) (V 1))& (bacc (pk 3) (b 0 0 17) (r 18) (pi1 x13)) & (bacc (pk 3) (b 0 1 19) (r 20) (pi2 x13)) qa21'_ss
			             (if_then_else_M (EQ_M (to x13) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x13)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x13)) qa12'_ss O)).


Definition qa02_sss := (if_then_else_M (EQ_M (to x13) (V 1)) qa12''_ss O).

(**************************************************************************)


Definition qa10_ssss := (if_then_else_M (EQ_M (to x12) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x12)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x12)) qa20_sss 
			          (if_then_else_M (EQ_M (to x12) (V 2)) qa11_sss O)).
 
Definition qa01_ssss :=  (if_then_else_M (EQ_M (to x12) (V 2))& (bacc (pk 3) (b 0 0 9) (r 10) (pi1 x12)) & (bacc (pk 3) (b 0 1 11) (r 12) (pi2 x12)) qa02_sss
			           (if_then_else_M (EQ_M (to x12) (V 1)) qa11'_sss O)).
(*************************************************************************)

Definition t15 :=  (if_then_else_M (EQ_M (to x1) (V 1)) qa10_ssss
		    	(if_then_else_M (EQ_M (to x1) (V 2))  qa01_ssss  O)).


(** ** Shuffle: performs lexicographic ordering terms *)


Definition pa22 := (shuf (dec qa22 (sk 5)) (dec  qa22_s (sk 5))).

(*******************************************************************************)

                                   

Definition pa21_s :=   (if_then_else_M (EQ_M (to x14) (V 2))&   (bacc (pk 3) (b 0 0 21) (r 22) (pi1 x14)) & (bacc (pk 3) (b 0 1 23) (r 24) (pi2 x14)) pa22 O).

Definition pa21'_s :=   (if_then_else_M (EQ_M (to x14) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x14)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x14)) pa22 O).

Definition pa12_s :=  (if_then_else_M (EQ_M (to x14) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x14)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x14)) pa22 O).

Definition pa12'_s :=  (if_then_else_M (EQ_M (to x14) (V 1))& (bacc (pk 3) (b 0 0 17) (r 18) (pi1 x14)) & (bacc (pk 3) (b 0 1 19) (r 20) (pi2 x14)) pa22 O).

Definition pa12''_s := (if_then_else_M (EQ_M (to x14) (V 1))& (bacc (pk 3) (b 0 0 25) (r 26) (pi1 x14)) & (bacc (pk 3) (b 0 1 27) (r 28) (pi2 x14)) pa22 O).

(***************************************************************************)


Definition pa20_ss := (if_then_else_M (EQ_M (to x13) (V 2)) pa21_s O).

Definition pa11_ss :=  (if_then_else_M (EQ_M (to x13) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x13)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x13)) pa21'_s
			           (if_then_else_M (EQ_M (to x13) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x13)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x13)) pa12_s O)).

Definition pa11'_ss :=  (if_then_else_M (EQ_M (to x13) (V 1))& (bacc (pk 3) (b 0 0 17) (r 18) (pi1 x13)) & (bacc (pk 3) (b 0 1 19) (r 20) (pi2 x13)) pa21'_s
			             (if_then_else_M (EQ_M (to x13) (V 2))&   (bacc (pk 3)  (b 0 0 13) (r 14) (pi1 x13)) & (bacc (pk 3) (b 0 1 15) (r 16) (pi2 x13)) pa12'_s O)).


Definition pa02_ss := (if_then_else_M (EQ_M (to x13) (V 1)) pa12''_s O).

(**************************************************************************)


Definition pa10_sss := (if_then_else_M (EQ_M (to x12) (V 1))& (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x12)) & (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x12)) pa20_ss 
			          (if_then_else_M (EQ_M (to x12) (V 2)) pa11_ss O)).
 
Definition pa01_sss :=  (if_then_else_M (EQ_M (to x12) (V 2))& (bacc (pk 3) (b 0 0 9) (r 10) (pi1 x12)) & (bacc (pk 3) (b 0 1 11) (r 12) (pi2 x12)) pa02_ss
			           (if_then_else_M (EQ_M (to x12) (V 1)) pa11'_ss O)).
(*************************************************************************)

Definition t16 :=  (if_then_else_M (EQ_M (to x1) (V 1)) pa10_sss 
		    	(if_then_else_M (EQ_M (to x1) (V 2))  pa01_sss  O)).
Definition phi15 := phi14 ++ [msg t16].


(** * ProtocolPhase2-II: if a voter votes for v1 in protocol I, then the voter votes for v2 in protocol II vice-versa *)

(** * Frame [phi25] *)

(** ** term [t24] *)
 
Definition qb22 := (if_then_else_M (EQ_M (to x15) (V 1))& (EQ_M (dv x15) (vt 1)) (chksign (pk 1) (sign (sk 1) (enc (pi2 x15) (pk 5) (r 29))))
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




(** Tactics *)

(*Ltac unf_mph := try unfold mphi10, mphi11, mphi12, mphi13, mphi20, mphi21, mphi22, mphi23.*)
 
Ltac unf_phi := try unfold phi0, phi11, phi12, phi13, phi14,  phi24, phi15, phi25.
 
Ltac unf_qa :=  try unfold  qa00, qa10, qa01; try unfold qa20, qa11, qa11', qa02, qa10_s, qa01_s; try unfold qa21, qa21', qa12, qa12', qa12'', qa20_s, qa11_s, qa11'_s, qa02_s,  qa10_ss, qa01_ss;try unfold qa22, qa21_s, qa21'_s, qa12_s, qa12'_s, qa12''_s, qa20_ss, qa11_ss, qa11'_ss, qa02_ss,  qa10_sss, qa01_sss; try unfold qa23, qa33, qa22_s, qa21_ss, qa21'_ss, qa12_ss, qa12'_ss, qa12''_ss, qa20_sss, qa11_sss, qa11'_sss, qa02_sss,  qa10_ssss, qa01_ssss.

Ltac unf_qb := try unfold qb22, qb21_s, qb21'_s, qb12_s, qb12'_s, qb12''_s, qb20_ss, qb11_ss, qb11'_ss, qb02_ss,  qb10_sss, qb01_sss; try unfold qb23, qb33, qb22_s, qb21_ss, qb21'_ss, qb12_ss, qb12'_ss, qb12''_ss, qb20_sss, qb11_sss, qb11'_sss, qb02_sss,  qb10_ssss, qb01_ssss.

Ltac unf_pa := try unfold pa22, pa21_s, pa21'_s, pa12_s, pa12'_s, pa12''_s, pa20_ss, pa11_ss, pa20_ss, pa11_ss, pa11'_ss, pa02_ss, pa10_sss, pa01_sss.

Ltac unf_pb := try unfold pb22, pb21_s, pb21'_s, pb12_s, pb12'_s, pb12''_s, pb20_ss, pb11_ss, pb20_ss, pb11_ss, pb11'_ss, pb02_ss, pb10_sss, pb01_sss.

Ltac unf_trm:=  try unfold t11, t12, t13, t14, t24.

Ltac unf := try unf_phi; try unf_trm; try unf_qa ; try unf_qb; try unf_pa; try unf_pb.

(** * Axioms and Definitions *)
Ltac funappmconst t H := apply FUNCApp_mconst with (m:= t) in H; simpl in H.

Ltac funappbconst b1 H := apply FUNCApp_bconst with (b:= b1) in H; simpl in H.

Ltac funappf1 f n H:= apply FUNCApp_f1 with (f1:= f) (p:= n) in H; simpl in H.

Ltac funappf2mb f n1 n2 H:= apply FUNCApp_f2b with (f2b:= f) (p1:= n1) (p2:= n2) in H; simpl in H.

Ltac funappf2m f n1 n2 H:= apply FUNCApp_f2m with (f2m:= f) (p1:= n1) (p2:= n2) in H; simpl in H.

Ltac funappf3mb f n1 n2 n3 H:= apply FUNCApp_f3b with (f3b:= f) (p1:= n1) (p2:= n2) (p3:= n3) in H; simpl in H.

Ltac funappf3m f n1 n2 n3 H:= apply FUNCApp_f3m with (f3m:= f) (p1:= n1) (p2:= n2) (p3:= n3) in H; simpl in H.

Ltac funappifm  n1 n2 n3 H:= apply FUNCApp_f3bm with (f3bm:= if_then_else_M) (p1:= n1) (p2:= n2) (p3:= n3) in H; simpl in H.

Ltac funappifb  n1 n2 n3 H:= apply FUNCApp_g3 with (g3:= if_then_else_B) (p1:= n1) (p2:= n2) (p3:= n3) in H; simpl in H.

Ltac funappf2b f n1 n2 H:= apply FUNCApp_f1 with (g2:= f ) (p1 := n1 ) (p2:= n2) in H; simpl in H.

Ltac retmylis H :=
  match goal with
    |[H: ?X ~ _  |- _ ] => pose (l := X)
  end.
Fixpoint eltPos  (x:oursum) {n} (l:mylist n) :nat :=
  match l with
    | [] => 0
    | h::t =>  if  (oursum_beq x h)  then 1 else S (eltPos x t)
  end.


Ltac funappeltPos2 tac f x y l H :=  retmylis H; tac f (eltPos x l) (eltPos y l) H; clear l.



Ltac funappeltPos3 tac x y z l H :=  tac  (eltPos x l) (eltPos y l) (eltPos z l) H; clear l.
 
Ltac aplyProjList l H1 :=
  match l with
    | [] => idtac
    | ?h :: ?t =>  simpl in H1; apply RESTR_proj with (p:= h) in H1; unfold proj_at_pos in H1; simpl in H1; 
                    aplyProjList t H1
  end.
 
 
(** Definitions *)

Fixpoint  repeat {A} (x : A) (n: nat ) :=
    match n with
      | 0 => []
      | S n' => x::(repeat x n')
    end. 



 

Fixpoint checksublis {m} (l: mylist m) {n} (l':mylist n) : bool :=
match (leb m n) , l with
  | true , [] => true
  | true , h :: t => if (checkmtmylis (ostomsg h) l') then (checksublis t l')
                     else false
  | _ , _ => false
end.

                    
 Fixpoint sublisIndcs {m} {n} (l :mylist m) (l': mylist n) : ilist nat m :=
  match  l with
    | [] => []
    | h :: t => (eltPos h l') :: (sublisIndcs t l')
  end.

 
 Fixpoint subtrmls_bol'(t: Bool) : list message :=
  match t with 
    | EQ_B  b1 b2 =>  (app (subtrmls_bol' b1) (subtrmls_bol' b2) )
    | EQ_M t1 t2 => (app (subtrmls_msg' t1) (subtrmls_msg' t2) )
    | if_then_else_B t1 t2 t3 => (app (subtrmls_bol' t1) (app (subtrmls_bol' t2) (subtrmls_bol' t3)))
    | EQL t1 t2 => (app (subtrmls_msg' t1) (subtrmls_msg' t2) )
    | ver t1 t2 t3 => (app (subtrmls_msg' t1) (app (subtrmls_msg' t2) (subtrmls_msg' t3)))
    | bver t1 t2 t3 => (app (subtrmls_msg' t1) (app (subtrmls_msg' t2) (subtrmls_msg' t3)))
    | bacc t1 t2 t3 t4 => (app (subtrmls_msg' t1) (app (subtrmls_msg' t2) (app (subtrmls_msg' t3) (subtrmls_msg' t4)) ))
    | _ => nil
 end
with subtrmls_msg' (t:message) : list message :=
       match t with 
         | if_then_else_M b3 t1 t2 => (app (subtrmls_bol' b3) (app (subtrmls_msg' t1) (subtrmls_msg' t2)))
         | (Mvar n') => (cons (Mvar n') nil)
         | acc => (cons acc nil)
         | lnc => (cons lnc nil)
         | lsk => (cons lsk nil)
         | O => (cons O nil)
         | N n'=> (cons (N n') nil)
         | new =>  (cons new nil)
         | exp t1 t2 t3 => (app (subtrmls_msg' t1) (app (subtrmls_msg' t2) (subtrmls_msg' t3)))
         | pair t1 t2 =>  (app (subtrmls_msg'  t1) (subtrmls_msg' t2) )
         | pi1 t1 => match t1 with
                       | k _ => (cons (pi1 t1) nil)
                       | _ => nil
                     end
         | pi2 t1 => match t1 with
                       | k _ => (cons (pi2 t1) nil)
                       | _ => nil
                     end
         | ggen t1 =>  (subtrmls_msg' t1)
         | act t1 =>  (subtrmls_msg' t1)
         | rr t1 =>  (subtrmls_msg' t1) 
         | rs t1 =>  (subtrmls_msg' t1) 
         | L t1 =>  (subtrmls_msg' t1) 
         | m t1 =>  (subtrmls_msg' t1) 
         | enc t1 t2 t3 => (app (subtrmls_msg' t1) (app (subtrmls_msg' t2) (subtrmls_msg' t3)))
         | dec t1 t2 =>  (app (subtrmls_msg' t1) (subtrmls_msg' t2))
         | k t1 =>  (subtrmls_msg' t1) 
         | nc n => (cons (nc n) nil) 
         | to t1 =>  (subtrmls_msg' t1) 
         | reveal t1 =>  (subtrmls_msg' t1) 
         | sign t1 t2 =>   (app (subtrmls_msg' t1) (subtrmls_msg' t2))
         (** Foo function protocol *)
         | commit t1 t2 t3 =>  (app (subtrmls_msg' t1) (app (subtrmls_msg' t2) (subtrmls_msg' t3)))
         | open t1 t2 t3 =>  (app (subtrmls_msg' t1) (app (subtrmls_msg' t2) (subtrmls_msg' t3)))
         | blind t1 t2 t3 =>  (app (subtrmls_msg' t1) (app (subtrmls_msg' t2) (subtrmls_msg' t3)))
         | unblind t1 t2 t3 t4 =>  (app (subtrmls_msg' t1) (app (subtrmls_msg' t2) (app (subtrmls_msg' t3) (subtrmls_msg' t4))))
         | v t1 => (cons (v t1) nil)
         | ok => (cons ok nil)
         | bsign t1 t2 =>   (app (subtrmls_msg' t1) (subtrmls_msg' t2))
         | f l =>  (@subtrmls subtrmls_msg' l)
         | _ => nil
       end.

 Eval compute in subtrmls_msg' (f [k (N 0) ; O]).
 Eval compute in subtrmls_msg' (sk 1).
 
Eval compute in (subtrmls_msg' (sign (if_then_else_M TRue (dec O (sk 1)) O) new)).

(** Subterms of [oursum] term. *)

Definition subtrmls_os' (t:oursum) : list message :=
  match t with 
    | msg t1 => subtrmls_msg' t1
    | bol b1 =>  subtrmls_bol' b1
  end.

(** Subterms of terms of type [mylist n] for some [n].*)

Fixpoint subtrmls_mylis' {n} (l:mylist n) : list message :=
  match l with 
    | [] => nil
    | h:: t => (app (subtrmls_os' h) (subtrmls_mylis' t))
  end.
 
 Axiom restr_sublis : forall {m} {n} (l1 l2 : mylist m) (l1' l2': mylist n) ,  l1 ~ l2 -> (andb (checksublis l1' l1) (checksublis l2' l2)  = true ) -> (sublisIndcs l1' l1) = (sublisIndcs l2' l2)-> l1' ~ l2'.

 Ltac restrsublis H :=
   match goal with
     | [|- ?X ~ ?Y] => apply restr_sublis with (l1':= X) (l2':=Y) in H; simpl in H
   end.

Definition topsymsg_beq (t t': message ) : bool :=
   match t, t' with
     | if_then_else_M  _ _ _ , if_then_else_M _ _ _ => true
     | if_then_else_M  _ _ _ , _ => false
     | Mvar _ , Mvar _  => true
     | Mvar _ , _  => false                            
     | exp _ _ _ , exp _ _ _ => true
     | exp _ _ _ , _ => false
     | pair _ _, pair _ _ => true
     | pair _ _,  _ => false
     | pi1 _ , pi1 _ => true
     | pi1 _ , _ => false
     | pi2 _ , pi2 _ => true
     | pi2 _ ,  _ => false
     | ggen _ , ggen _ => true
     | ggen _ ,  _ =>  false
     | act _ , act _  => true
     | act _ , _  => false
     | rr _, rr _ => true
     | rr _,  _ => false
     | rs _, rs _ => true
     | rs _, _ => false
     | L _, L _ => true
     | L _, _ => false
     | m _, m _  => true
     | m _, _  => false
     | enc _ _ _, enc _ _ _ => true
     | enc _ _ _, _ => false
     | dec _ _, dec _ _ => true
     | dec _ _, _ => false
     | k _ , k _ =>  true
     | k _ , _ =>  false
     | nc _, nc _ => true
     | nc _,  _ => false
     | to _, to _ => true
     | to _, _ => false
     | reveal _, reveal _ => true
     | reveal _, _ => false
     | sign _ _, sign _ _ =>  true
     | sign _ _, _ =>  false
     | f _ , f _ => true
     | f _ , _ => false
     (** foo function symbol *)
     | commit _ _ _, commit _ _ _ => true
     | commit _ _ _, _ => false
     | open _ _ _, open _ _ _ => true
     | open _ _ _, _ => false
     | blind _ _ _, blind _ _ _  =>  true
     | blind _ _ _ , _  =>  false
     | unblind _ _ _ _, unblind _ _ _ _ => true
     | unblind _ _ _ _, _  => false
     | bsign _ _, bsign _ _ => true
     | bsign _ _,  _ => false
     | v _ , v _=>  true
     | v _ , _ => false
     | _ , _=> message_beq t t'
   end.

 Definition topsybol_beq (b b' : Bool) : bool :=
   match b, b' with
     | Bvar _, Bvar _ =>  true
     | EQ_B  _ _ , EQ_B _ _  =>  true
     | EQ_M _ _, EQ_M _ _ =>  true
     | if_then_else_B _ _ _, if_then_else_B _ _ _ => true
     | EQL _ _ , EQL _ _ => true
     | ver _ _ _, ver _ _ _ => true
     | bver _ _ _, bver _ _ _ => true
     | bacc _ _ _ _, bacc _ _ _ _  =>true
     | Bvar _,  _ =>  false
     | EQ_B  _ _ , _  =>  false
     | EQ_M _ _,   _ =>  false
     | if_then_else_B _ _ _,  _ => false
     | EQL _ _ , _ => false
     | ver _ _ _,  _ => false
     | bver _ _ _, _ => false
     | bacc _ _ _ _, _  =>false
     | _ , _ => Bool_beq b b'
   end.
 Eval compute in topsymsg_beq (if_then_else_M _ _ _) O.

Definition topsyos_beq (t1 t2 : oursum): bool :=
  match t1 , t2 with
      | msg t1', msg t2' => topsymsg_beq t1' t2'
      | bol b1, bol b2 => topsybol_beq b1 b2
      | _ , _ => false
  end.
            
           
 
(** * Assumptions *)
(** blinds of two indistinguishable messages are also indistinguishable *)
(** Signatures of two indistinguishable messages are also indistinguishable *)
 
 

 
Fixpoint eltPos' (x:oursum) {n} (l:mylist n) :nat :=
  match l with
    | [] => 0
    | h::t =>  if  (oursum_beq x h)  then 1 else S (eltPos x t)
  end.
Fixpoint checkostmylis (x:oursum) {n} (l:mylist n) : bool :=
  match l with
    | [] => false
    | h :: t => if (oursum_beq x h) then true else (checkostmylis x t)
  end.

Fixpoint checksublis'  (l: list oursum) {n} (l':mylist n) : bool :=
match (leb n n) , l with
  | true , nil => true
  | true , cons h t => if (checkostmylis h  l') then (checksublis' t l')
                     else false
  | _ , _ => false
end.

                    
 Fixpoint  sublisIndcs'  {n} (l :list oursum) (l': mylist n) : list nat :=
  match  l with
    | nil => nil
    | cons h t => cons (eltPos h l')  (sublisIndcs' t l')
  end.


Check subtrmls.

Print subtrmls. 
Section subtrm'.
Variable f: message -> list oursum.
Fixpoint mapsubtrmls (l: list message) : list oursum :=
  match l with
    | nil => nil
    | cons h t => (app (f h) (mapsubtrmls t))
  end.
End subtrm'.
Fixpoint subtrmls_bol''(t: Bool) : list oursum :=
  match t with 
    | EQ_B  b1 b2 =>  (app (subtrmls_bol'' b1) (subtrmls_bol'' b2) )
    | EQ_M t1 t2 => (app (subtrmls_msg'' t1) (subtrmls_msg'' t2) )
    | if_then_else_B t1 t2 t3 => (app (subtrmls_bol'' t1) (app (subtrmls_bol'' t2) (subtrmls_bol'' t3)))
    | EQL t1 t2 => (app (subtrmls_msg'' t1) (subtrmls_msg'' t2) )
    | ver t1 t2 t3 => (app (subtrmls_msg'' t1) (app (subtrmls_msg'' t2) (subtrmls_msg'' t3)))
    | bver t1 t2 t3 => (app (subtrmls_msg'' t1) (app (subtrmls_msg'' t2) (subtrmls_msg'' t3)))
    | bacc t1 t2 t3 t4 => (app (subtrmls_msg'' t1) (app (subtrmls_msg'' t2) (app (subtrmls_msg'' t3) (subtrmls_msg'' t4))))
    | _ => nil
 end
with subtrmls_msg'' (t:message) : list oursum :=
       match t with 
         | if_then_else_M b3 t1 t2 => (app (subtrmls_bol'' b3) (app (subtrmls_msg'' t1) (subtrmls_msg'' t2))) 
         | (Mvar n') => (cons (msg (Mvar n')) nil)
         | acc => (cons (msg acc) nil)
         | lnc => (cons (msg lnc) nil)
         | lsk => (cons (msg lsk) nil)
         | O => (cons (msg O) nil)
         | N n'=> (cons (msg (N n')) nil)
         | new =>  (cons (msg new) nil)
         | exp t1 t2 t3 => (app (subtrmls_msg'' t1) (app (subtrmls_msg'' t2) (subtrmls_msg'' t3)))
         | pair t1 t2 =>  (app (subtrmls_msg''  t1) (subtrmls_msg'' t2) )
         | pi1 t1 => match t1 with
                       | k _ => (cons (msg (pi1 t1)) nil)
                       | _ => nil
                     end
         | pi2 t1 => match t1 with
                       | k _ => (cons (msg (pi2 t1)) nil)
                       | _ => nil
                     end
         | ggen t1 =>  (subtrmls_msg'' t1)
         | act t1 =>  (subtrmls_msg'' t1)
         | rr t1 =>  (subtrmls_msg'' t1) 
         | rs t1 =>  (subtrmls_msg'' t1) 
         | L t1 =>  (subtrmls_msg'' t1) 
         | m t1 =>  (subtrmls_msg'' t1) 
         | enc t1 t2 t3 => (app (subtrmls_msg'' t1) (app (subtrmls_msg'' t2) (subtrmls_msg'' t3)))
         | dec t1 t2 =>  (app (subtrmls_msg'' t1) (subtrmls_msg'' t2))
         | k t1 =>  (subtrmls_msg'' t1) 
         | nc n => (cons (msg (nc n)) nil) 
         | to t1 =>  (subtrmls_msg'' t1) 
         | reveal t1 =>  (subtrmls_msg'' t1) 
         | sign t1 t2 =>   (app (subtrmls_msg'' t1) (subtrmls_msg'' t2))
         (** Foo function protocol *)
         | commit t1 t2 t3 =>  (cons (msg t) nil)
         | open t1 t2 t3 =>  (app (subtrmls_msg'' t1) (app (subtrmls_msg'' t2) (subtrmls_msg'' t3))) 
         | blind t1 t2 t3 =>  (cons (msg t) nil)
         | unblind t1 t2 t3 t4 =>  (app (subtrmls_msg'' t1) (app (subtrmls_msg'' t2) (app (subtrmls_msg'' t3) (subtrmls_msg'' t4))))
         | v t1 => (cons (msg (v t1)) nil)
         | V n => (cons (msg (V n)) nil)
         | ok => (cons (msg ok) nil)
         | bsign t1 t2 =>   (app (subtrmls_msg'' t1) (subtrmls_msg'' t2))
         | f l =>  (@mapsubtrmls subtrmls_msg'' l)
         | _ => nil
       end.

 Eval compute in subtrmls_msg'' (f [k (N 0) ; O]).
 Eval compute in subtrmls_msg'' (sk 1).
 
Eval compute in (subtrmls_msg'' (sign (if_then_else_M TRue (dec O (sk 1)) O) new)).

(** Subterms of [oursum] term. *)

Definition subtrmls_os'' (t:oursum) : list oursum :=
  match t with 
    | msg t1 => subtrmls_msg'' t1
    | bol b1 =>  subtrmls_bol'' b1
  end.

(** Subterms of terms of type [mylist n] for some [n].*)

Fixpoint subtrmls_mylis'' {n} (l:mylist n) : list oursum :=
  match l with 
    | [] => nil
    | h:: t => (app (subtrmls_os'' h) (subtrmls_mylis'' t))
  end.
  
 
(** Tactics *)

(** Projection n times *)
Ltac aplyprojn n n' H:=
  match n with
    | 0 => idtac
    | S ?n'' => aplyProjList  [n'] H; simpl in H; aplyprojn n'' n' H
  end.
Axiom funapptrm : forall {m} (t1 t2 : oursum) (l1 l2 : mylist m),  l1 ~ l2 -> (topsyos_beq t1 t2 = true ) -> (andb (checksublis' (subtrmls_os'' t1)  l1) (checksublis' (subtrmls_os'' t2) l2) = true) ->  (sublisIndcs' (subtrmls_os'' t1) l1) = (sublisIndcs' (subtrmls_os'' t2) l2) -> (l1 ++ [ t1]) ~ (l2 ++ [ t2]).

Ltac funapptrmhyp m1 m2 H :=
  apply funapptrm with (t1 := m1) (t2 := m2) in H; simpl in H .
 
 (** blindness *) 
Ltac aply_blindnes n n1 n2 n3 n4 m0 m1 t1 t2 t3 t4 l H H0  := pose proof( blindness n n1 n2 n3 n4 m0 m1 t1 t2 t3 t4 l ) as H ;
assert( H0:  (Fresh [n1; n2; n3; n4] (l++[ msg (N n); msg m0; msg m1]) = true) /\ (check_rn_blind_listm [n1;n2;n3;n4] [t1;t2;t3;t4] = true)); try split; try reflexivity;
apply H0 in H; clear H; simpl in H.

(** Using [funapptrmhyp] *)
Ltac appconst H:=
  funappmconst ok H; funappmconst (V 1) H; funappmconst (V 2) H; funappmconst O H; try reflexivity.

(** Proof of phase2*)

Theorem phase2ind: phi15 ~ phi25.
Proof. repeat unf. simpl. 
       unfold t16, t26.
apply IFBRANCH_M1 with (ml1:= phi14) (ml2:=phi14).
simpl. 
unfold pa10_sss, pb10_sss.  
apply IFBRANCH_M1 with (ml1:= (phi14 ++ [
  bol (EQ_M (to x1) (V 1))])) (ml2:= (phi24 ++ [bol (EQ_M (to x1) (V 1))])).
simpl.

apply IFBRANCH_M1 with (ml1:=  (phi14 ++ [
  bol (EQ_M (to x1) (V 1)); bol  ((EQ_M (to x12) (V 1)) & (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x12))) &
         (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x12)) ])) (ml2:= (phi14 ++ [
  bol (EQ_M (to x1) (V 1)); bol  ((EQ_M (to x12) (V 1)) & (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x12))) &
         (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x12)) ])).
simpl.

 apply IFBRANCH_M1 with (ml1:=  (phi14 ++ [
  bol (EQ_M (to x1) (V 1)); bol  ((EQ_M (to x12) (V 1)) & (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x12))) &
         (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x12)) ;  bol (EQ_M (to x13) (V 2)) ])) (ml2:= (phi14 ++ [
  bol (EQ_M (to x1) (V 1)); bol  ((EQ_M (to x12) (V 1)) & (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x12))) &
         (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x12)) ;  bol (EQ_M (to x13) (V 2)) ])).
 simpl.
 unfold pa22, pb22.
 unfold qa22, qa22_s, qb22, qb22_s.
 repeat rewrite getmsg. 
  assert(forall n t1 t2 t3 t4 t1', (shuf (dec (if_then_else_M (Bvar n) t1 t2) t1' ) (dec (if_then_else_M (Bvar n) t3 t4) t1')) # (if_then_else_M (Bvar n) (shuf (dec t1 t1') (dec t3 t1') ) (shuf (dec t2 t1') (dec t4 t1')))).
 intros.
rewrite <- IFSAME_M with (x:= (shuf (dec (if_then_else_M (Bvar n) t1 t2) t1')
      (dec (if_then_else_M (Bvar n) t3 t4) t1'))) (b:= (Bvar n)).
rewrite IFEVAL_M. 
simpl.
rewrite <- beq_nat_refl.
repeat rewrite IFTRUE_M.
repeat rewrite IFFALSE_M. 
rewrite IFEVAL_M with (t1:= (shuf (dec t1 t1') (dec t3 t1'))). reflexivity.
  
Axiom ifmorph_shuffle: forall b1 t1 t2 t3 t4 t5 , (shuf (dec (if_then_else_M b1 t1 t2) t5 ) (dec (if_then_else_M b1 t3 t4) t5)) # (if_then_else_M b1 (shuf (dec t1 t5) (dec t3 t5) ) (shuf (dec t2 t5) (dec t4 t5))).
Axiom ifmorph_shuffle1: forall b1 t1 t2 t3  t5 , (shuf (dec (if_then_else_M b1 t1 t2) t5 ) (dec t3 t5)) # (if_then_else_M b1 (shuf (dec t1 t5) (dec t3 t5) ) (shuf (dec t2 t5) (dec t3 t5))).
Axiom ifmorph_shuffle2: forall b1 t1 t2 t3  t5 , (shuf (dec t1 t5 ) (dec (if_then_else_M b1 t2 t3) t5)) # (if_then_else_M b1 (shuf (dec t1 t5) (dec t2 t5) ) (shuf (dec t1 t5) (dec t3 t5))). 


Axiom andB_elm': forall (b1 b2: Bool) (x y : message), (if_then_else_M b1& b2 x y) #  (if_then_else_M b1 (if_then_else_M b2 x y ) y).
repeat rewrite andB_elm'.
repeat rewrite ifmorph_shuffle.
repeat rewrite ifmorph_shuffle1.
repeat rewrite ifmorph_shuffle2. 
apply IFBRANCH_M1 with (ml1:= (phi14++ [bol (EQ_M (to x1) (V 1));
    bol
      ((EQ_M (to x12) (V 1)) & (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x12))) &
      (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x12)); bol (EQ_M (to x13) (V 2));
    bol
      ((EQ_M (to x14) (V 2)) & (bacc (pk 3) (b 0 0 21) (r 22) (pi1 x14))) &
      (bacc (pk 3) (b 0 1 23) (r 24) (pi2 x14))])) (ml2:= (phi14++ [bol (EQ_M (to x1) (V 1));
    bol
      ((EQ_M (to x12) (V 1)) & (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x12))) &
      (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x12)); bol (EQ_M (to x13) (V 2));
    bol
      ((EQ_M (to x14) (V 2)) & (bacc (pk 3) (b 0 0 21) (r 22) (pi1 x14))) &
      (bacc (pk 3) (b 0 1 23) (r 24) (pi2 x14))])).
simpl.
apply IFBRANCH_M1 with (ml1:= (phi14++ [bol (EQ_M (to x1) (V 1));
    bol
      ((EQ_M (to x12) (V 1)) & (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x12))) &
      (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x12)); bol (EQ_M (to x13) (V 2));
    bol
      ((EQ_M (to x14) (V 2)) & (bacc (pk 3) (b 0 0 21) (r 22) (pi1 x14))) &
      (bacc (pk 3) (b 0 1 23) (r 24) (pi2 x14)) ;  bol (EQ_M (to x15) (V 1))])) (ml2:= (phi14++ [bol (EQ_M (to x1) (V 1));
    bol
      ((EQ_M (to x12) (V 1)) & (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x12))) &
      (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x12)); bol (EQ_M (to x13) (V 2));
    bol
      ((EQ_M (to x14) (V 2)) & (bacc (pk 3) (b 0 0 21) (r 22) (pi1 x14))) &
      (bacc (pk 3) (b 0 1 23) (r 24) (pi2 x14)) ;  bol (EQ_M (to x15) (V 1))])).
simpl.
unfold qa23, qb23.

repeat rewrite getmsg.
repeat rewrite andB_elm'.

repeat rewrite ifmorph_shuffle2.
apply IFBRANCH_M1 with (ml1:= ([msg (pk 0); msg (pk 1); msg (pk 2); msg (N 4); 
    msg (N 5); msg qa00; msg t11; msg t12; msg t13; 
    bol (EQ_M (to x1) (V 1));
    bol
      ((EQ_M (to x12) (V 1)) & (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x12))) &
      (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x12)); bol (EQ_M (to x13) (V 2));
    bol
      ((EQ_M (to x14) (V 2)) & (bacc (pk 3) (b 0 0 21) (r 22) (pi1 x14))) &
      (bacc (pk 3) (b 0 1 23) (r 24) (pi2 x14)); bol (EQ_M (to x15) (V 1));
    bol (EQ_M (dv x15) (vt 1))])) (ml2:=  [msg (pk 0); msg (pk 1); msg (pk 2); msg (N 4); 
   msg (N 5); msg qa00; msg t11; msg t12; msg t13; 
   bol (EQ_M (to x1) (V 1));
   bol
     ((EQ_M (to x12) (V 1)) & (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x12))) &
     (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x12)); bol (EQ_M (to x13) (V 2));
   bol
     ((EQ_M (to x14) (V 2)) & (bacc (pk 3) (b 0 0 21) (r 22) (pi1 x14))) &
     (bacc (pk 3) (b 0 1 23) (r 24) (pi2 x14)); bol (EQ_M (to x15) (V 1));
   bol (EQ_M (dv x15) (vt 1))]) .
simpl.

apply IFBRANCH_M1 with (ml1:= ([msg (pk 0); msg (pk 1); msg (pk 2); msg (N 4); 
    msg (N 5); msg qa00; msg t11; msg t12; msg t13; 
    bol (EQ_M (to x1) (V 1));
    bol
      ((EQ_M (to x12) (V 1)) & (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x12))) &
      (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x12)); bol (EQ_M (to x13) (V 2));
    bol
      ((EQ_M (to x14) (V 2)) & (bacc (pk 3) (b 0 0 21) (r 22) (pi1 x14))) &
      (bacc (pk 3) (b 0 1 23) (r 24) (pi2 x14)); bol (EQ_M (to x15) (V 1));
    bol (EQ_M (dv x15) (vt 1)); bol (EQ_M (to x16) (V 2))]))(ml2:= ([msg (pk 0); msg (pk 1); msg (pk 2); msg (N 4); 
    msg (N 5); msg qa00; msg t11; msg t12; msg t13; 
    bol (EQ_M (to x1) (V 1));
    bol
      ((EQ_M (to x12) (V 1)) & (bacc (pk 3) (b 0 0 5) (r 6) (pi1 x12))) &
      (bacc (pk 3) (b 0 1 7) (r 8) (pi2 x12)); bol (EQ_M (to x13) (V 2));
    bol
      ((EQ_M (to x14) (V 2)) & (bacc (pk 3) (b 0 0 21) (r 22) (pi1 x14))) &
      (bacc (pk 3) (b 0 1 23) (r 24) (pi2 x14)); bol (EQ_M (to x15) (V 1));
    bol (EQ_M (dv x15) (vt 1)); bol (EQ_M (to x26) (V 2))])).
simpl.
Axiom dec_enc: forall n n' t, (dec (enc t (pk n) (r n')) (sk n)) # t.
repeat rewrite dec_enc.

(*
 pose proof (blindness2 3 5 6 7 8 21 22 23 24  0 1 (v (N 0)) (v (N 1))
                       (commit (pk 0) (Mvar 0) (r 5)) (commit (pk 0) (Mvar 1) (r 7)) (commit (pk 0) (Mvar 0) (r 21)) (commit (pk 0) (Mvar 1) (r 23)) ( (blind (pk 3) (commit (pk 0) (Mvar 0) (r 5)) (r 6)),(blind (pk 3) (commit (pk 0) (Mvar 0) (r 7)) (r 8)))  ( (blind (pk 3) (commit (pk 0) (Mvar 0) (r 21)) (r 22)),(blind (pk 3) (commit (pk 0) (Mvar 0) (r 23)) (r 24)))  (bsign (sk 3) ( (blind (pk 3) (commit (pk 0) (Mvar 0) (r 5)) (r 6)),(blind (pk 3) (commit (pk 0) (Mvar 0) (r 7)) (r 8))))  (bsign (sk 3) ( (blind (pk 3) (commit (pk 0) (Mvar 0) (r 21)) (r 22)),(blind (pk 3) (commit (pk 0) (Mvar 0) (r 23)) (r 24))))) [msg (pk 0); msg (pk 1); msg (pk 2); msg (N 4); msg (N 5) ; msg (sk 1) ; msg (sk 2)].
assert(Fresh [5; 6; 7; 8; 21; 22; 23; 24]
         ([msg (pk 0); msg (pk 1); msg (pk 2); msg (N 4); msg (N 5); msg (sk 1) ; msg (sk 2)] ++
          [msg (N 3); msg (v (N 0)); msg (v (N 1))]) = true ->
       let mvl := (cons 0 (cons 1 nil)) in
       mvars_msg (commit (pk 0) (Mvar 0) (r 5), commit (pk 0) (Mvar 1) (r 7)) =
       mvl /\
       mvars_msg
         (commit (pk 0) (Mvar 0) (r 21), commit (pk 0) (Mvar 1) (r 23)) = mvl).
intros. split. simpl. reflexivity. reflexivity.
apply H0 in H1.
clear H0.  simpl in H1.*)
Abort.

Ltac x1checks H := funapptrmhyp (msg x1) (msg x1) H; try reflexivity;
                   funapptrmhyp (msg (to x1)) (msg (to x1)) H; try reflexivity;
                   funapptrmhyp (bol (EQ_M (to x1) (V 1))) (bol (EQ_M (to x1) (V 1))) H; try reflexivity;
                   funapptrmhyp (bol (EQ_M (to x1) (V 2))) (bol (EQ_M (to x1) (V 2))) H; try reflexivity.

Ltac funappsign n f t1 t2 H:=  funapptrmhyp (msg (f (sk n) t1)) (msg (f (sk n) t2)) H; try reflexivity.
Ltac paire1e2 t1 t2 H:= funapptrmhyp (msg (t1 , t2)) (msg (t1, t2))  H;try reflexivity.

Ltac e1e1' n v1 v2 n1 n2 n3 n4 H := funapptrmhyp (msg (sign (sk n) (e 3 (b 0 v1 n1) n2)))  (msg (sign (sk n) (e 3 (b 0 v2 n3) n4))) H;try reflexivity.


Ltac baccr6r10 v1 v2 n1 n2 n3 n4 t1 t2 H:= funapptrmhyp (bol (bacc (pk 3) (b 0 v1 n1) (r n2) (pi1 t1 ))) (bol (bacc (pk 3) (b 0 v2 n3)  (r n4) (pi1 t2))) H; try reflexivity.

Ltac aply_andB t1 t2  H := funapptrmhyp  t1 t2 H; try reflexivity.

End foo_prot1.
