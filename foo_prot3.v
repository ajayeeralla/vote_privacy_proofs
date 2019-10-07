Load "tactics".

 
(** * FOO Voting Prtocol *)
(** ** Phase-I *)
(** 
- V -> A : (V, sign(blind(commit(v, r), r'), sk(V)))

- A-> V :  sign(blind(commit(v, r), r'), sk(A)) *)

Section foo_prot2.   
 
(** - We assume that Administrator is honest, and collector is dishonest
    - Hence, random numbers used to generate keys (pair) of them included in attacker's knowledge *)

(** * ProtocolPhase-I: There are two voters [V1] and [V2], and their corresponding votes [va] and [vb] respectively. *)
 
(** * Frame [phi0]: initial knowledge *)
(** 1-Voter1, 2-Voter2, 3-Administrator, 4-Collector, 5-Mixnet 
[(pk 0)] represents a public key used in commitment shceme. *) 
 
   
Definition vt (n:nat) := (v (N n)).
Definition phi0:= [msg (pk 0); msg (pk 1); msg (pk 2);  msg (pk 3); msg (N 4); msg (pk 5)].

(** * Frame [phi111] *)

(** commitments *) 
 
Definition b (n' n'':nat) := (commit (pk 0) (v (N n')) (r n'')).
Definition e (t:message) (n':nat) := (blind t (pk 3) (r n')).


(** Converting [mylist] to [list message] *)
 

Definition mphi0 := (conv_mylist_listm phi0).

(** attacker's computation *)

Definition x11 := (f mphi0).  
   
(** next step *)     
Definition achecks (x1: message) := (eqm (to x11) (pk 3)) & (ver (pi1 (pi1 x11))  (pi1 (pi2 (pi1 x11))) (pi2 (pi2 (pi1 x11)))) & (ver (pi1 (pi2 x11))  (pi1 (pi2 (pi2 x11))) (pi2 (pi2 (pi2 x11)))).

Definition admin (x1:message) :=  (ifm (achecks (x1))  ((bsign (sk 3)  (pi1 (pi2 (pi1 x11)))),  (bsign (sk 3)  (pi1 (pi2 (pi2 x11))))) O).
   
Definition qa0 :=  (ifm (eqm (to x11) (V 1)) ((pk 1), ((e (b 0 7) 8) , (sign (sk 1) (e (b 0 7) 8))))
		    	            (ifm  (eqm (to x11) (V 2))  ((pk 2), ( (e (b 1 9) 10),  (sign (sk 2) (e (b 1 9) 10))))
                                                 (admin x11)   )).
                                                                     

(** attacker's knowledge *)

Definition phi11 := phi0 ++ [msg qa0 ].


(** * Frame [phi2] *) 
 
Definition mphi11 := (conv_mylist_listm (phi11 )).
Definition x12 := (f (mphi11 )).  
    
Definition qa1 := (ifm (eqm (to x12) (V 1))& (bacc (pk 3) (b 0 7) (r 8) (pi1 x12))  ok 
			           (ifm (eqm (to x12) (V 2))  ((pk 2), ( (e (b 1 11) 12),  (sign (sk 2) (e (b 1 11) 12))))
                                                   (admin x12))). 
 
Definition qa2 :=  (ifm (eqm (to x12) (V 2))& (bacc (pk 3) (b 1 9) (r 10) (pi2 x12))  ok 
			           (ifm (eqm (to x12) (V 1))  ((pk 1), ( (e (b 0 13) 14),  (sign (sk 1) (e (b 0 13) 14))))
                                                   (admin x12))).
 
Definition qa3 := (ifm (eqm (to x12) (V 1)) ((pk 1), ((e (b 0 15) 16) , (sign (sk 1) (e (b 0 15) 16))))
		    	            (ifm  (eqm (to x12) (V 2))  ((pk 2), ( (e (b 1 17) 18),  (sign (sk 2) (e (b 1 17) 18)))) O)).

Definition t11 :=  (ifm (eqm (to x11) (V 1)) (qa1 )
		    	           (ifm (eqm (to x11) (V 2))  (qa2 )
                                                   (ifm (achecks x11) (qa3 )
                                                                   O))).

Definition phi12 := (phi11 ) ++ [msg (t11 )].


(** * Frame [phi13] *)

Definition mphi2 := (conv_mylist_listm (phi12 )).
Definition x13 := (f (mphi2 )). 
    
Definition qa11 :=  (ifm  (eqm (to x13) (V 2))  ((pk 2), ( (e (b 1 19) 20),  (sign (sk 2) (e (b 1 19) 20))))
                                      (admin x13)).
 
Definition qa12 := (ifm (eqm (to x13) (V 1))& (bacc (pk 3) (b 0 7) (r 8) (pi2 x12)) ok
                                    (ifm (eqm (to x13) (V 2))& (bacc (pk 3) (b 1 11) (r 12) (pi2 x12)) ok
                                                    (admin x13))).
 
Definition qa13 := (ifm (eqm (to x13) (V 1))& (bacc (pk 3) (b 0 7) (r 8) (pi2 x12)) ok
                                    (ifm  (eqm (to x13) (V 2))  ((pk 2), ( (e (b 1 21) 22),  (sign (sk 2) (e (b 1 21) 22)))) O)).


Definition qa21 := (ifm  (eqm (to x13) (V 1))  ((pk 1), ( (e (b 0 23) 24),  (sign (sk 1) (e (b 0 23) 24))))
                                    (admin x13)).

Definition qa22 := (ifm (eqm (to x13) (V 1))& (bacc (pk 3) (b 0 13) (r 14) (pi1 x12)) ok
                                    (ifm (eqm (to x13) (V 2))& (bacc (pk 3) (b 1 9) (r 10) (pi2 x12)) ok
                                                    (admin x13))).
 
Definition qa23 := (ifm (eqm (to x13) (V 2))& (bacc (pk 3) (b 1 9) (r 10) (pi2 x12)) ok
                        (ifm  (eqm (to x13) (V 1))  ((pk 1), ( (e (b 0 25) 26),  (sign (sk 1) (e (b 0 25) 26)))) O)).

 
Definition qa31 := (ifm (eqm (to x13) (V 1))& (bacc (pk 3) (b 0 15) (r 16) (pi1 x12)) ok
                                    (ifm  (eqm (to x13) (V 2))  ((pk 2), ( (e (b 1 27) 28),  (sign (sk 2) (e (b 1 27) 28)))) O)).

Definition qa32 := (ifm (eqm (to x13) (V 2))& (bacc (pk 3) (b 1 17) (r 18) (pi2 x12)) ok
                                    (ifm  (eqm (to x13) (V 1))  ((pk 1), ( (e (b 0 29) 30),  (sign (sk 1) (e (b 0 29) 30)))) O)).
(********************************************************************************************)

Definition qa1_s := (ifm (eqm (to x12) (V 1))& (bacc (pk 3) (b 0 7) (r 8) (pi1 x12))  (qa11 )
			           (ifm (eqm (to x12) (V 2))  (qa12 )
                                                  (ifm (achecks x12) (qa13 ) O))).
 
Definition qa2_s :=  (ifm (eqm (to x12) (V 2))& (bacc (pk 3) (b 1 9) (r 10) (pi2 x12))  (qa21 )
			           (ifm (eqm (to x12) (V 1))  (qa22 )
                                                   (ifm (achecks x12) (qa23 ) O))).
 
Definition qa3_s := (ifm (eqm (to x12) (V 1)) (qa31 )
		    	            (ifm  (eqm (to x12) (V 2))  (qa32 ) O)).

Definition t12 :=  (ifm (eqm (to x11) (V 1)) (qa1_s )
		    	           (ifm (eqm (to x11) (V 2))  (qa2_s )
                                                   (ifm (achecks x11) (qa3_s )
                                                                   O))).

Definition phi13  := (phi12 ) ++ [msg (t12 )].

(** * Frame [phi4] *)
  
Definition mphi13 := (conv_mylist_listm (phi13 )).
Definition x14 := (f (mphi13 )). 
  
Definition qa111 := (ifm  (eqm (to x14) (V 2))& (bacc (pk 3) (b 1 19) (r 20) (pi2 x12)) ok
                                     (admin x14)).
 
Definition qa112 := (ifm  (eqm (to x14) (V 2))  ((pk 2), ( (e (b 0 31) 32),  (sign (sk 2) (e (b 0 31) 32)))) O).
 
 (*************************************************)                       

  
Definition qa121 := (ifm (eqm (to x14) (V 2 ))& (bacc (pk 3) (b 1 11) (r 12) (pi2 x12)) ok
                         (admin x14)).

Definition qa122 := (ifm (eqm (to x14) (V 1 ))& (bacc (pk 3) (b 0 7) (r 8) (pi1 x12)) ok
                         (admin x14)).
 
Definition  qa123 := (ifm (eqm (to x14) (V 1 ))& (bacc (pk 3) (b 0 7) (r 8) (pi1 x12)) ok
                          (ifm (eqm (to x14) (V 2 ))& (bacc (pk 3) (b 1 11) (r 12) (pi2 x12)) ok
                               O)).
(****************************************************)

Definition qa131 := (ifm  (eqm (to x14) (V 2))  ((pk 2), ( (e (b 1 33) 34),  (sign (sk 2) (e (b 1 33) 34)))) O).
 
Definition qa132 :=  (ifm (eqm (to x14) (V 1 ))& (bacc (pk 3) (b 0 7) (r 8) (pi1 x12)) ok
                          (ifm (eqm (to x14) (V 2 ))& (bacc (pk 3) (b 1 21) (r 22) (pi2 x12)) ok
                               O)).
(****************************************************)
 
Definition qa211 :=  (ifm (eqm (to x14) (V 1 ))& (bacc (pk 3) (b 0 23) (r 24) (pi1 x12)) ok
                          (admin x14)).

Definition qa212 :=  (ifm  (eqm (to x14) (V 2))  ((pk 2), ( (e (b 1 35) 36),  (sign (sk 2) (e (b 1 35) 36)))) O).


(***************************************************)

Definition qa221 :=   (ifm (eqm (to x14) (V 2 ))& (bacc (pk 3) (b 1 9) (r 10) (pi2 x12)) ok
                           (admin x14)).
Definition qa222 :=  (ifm (eqm (to x14) (V 1 ))& (bacc (pk 3) (b 0 13) (r 14) (pi1 x12)) ok
                          (admin x14)).
Definition qa223 := (ifm (eqm (to x14) (V 1 ))& (bacc (pk 3) (b 0 13) (r 14) (pi1 x12)) ok
                         (ifm (eqm (to x14) (V 2 ))& (bacc (pk 3) (b 1 9) (r 10) (pi2 x12)) ok
                              O)).

(***************************************************)

Definition qa231 := (ifm (eqm (to x14) (V 1))  ((pk 1), ( (e (b 0 37) 38),  (sign (sk 2) (e (b 0 37) 38)))) O).
 
Definition qa232 := (ifm (eqm (to x14) (V 1 ))& (bacc (pk 3) (b 0 25) (r 26) (pi1 x12)) ok
                          (ifm (eqm (to x14) (V 2 ))& (bacc (pk 3) (b 1 9) (r 10) (pi2 x12)) ok
                               O)).
(***************************************************)

Definition qa311  := (ifm  (eqm (to x14) (V 2))  ((pk 2), ( (e (b 1 39) 40),  (sign (sk 2) (e (b 1 39) 40))))
                                                    O).
Definition qa312  :=  (ifm (eqm (to x14) (V 1 ))& (bacc (pk 3) (b 0 15) (r 16) (pi1 x12)) ok
                          (ifm (eqm (to x14) (V 2 ))& (bacc (pk 3) (b 1 27) (r 28) (pi2 x12)) ok
                               O)).

(****************************************)

Definition qa321  := (ifm  (eqm (to x14) (V 1))  ((pk 1), ( (e (b 0 41) 42),  (sign (sk 1) (e (b 0 41) 42)))) O).

Definition qa322 :=  (ifm (eqm (to x14) (V 1 ))& (bacc (pk 3) (b 0 29) (r 30) (pi1 x12)) ok
                          (ifm (eqm (to x14) (V 2 ))& (bacc (pk 3) (b 1 17) (r 18) (pi2 x12)) ok
                               O)).

(*****************************************)
  
Definition qa11_s :=  (ifm  (eqm (to x13) (V 2)) (qa111 )
                                      (ifm (achecks x13) (qa112 )  O)).
 
Definition qa12_s := (ifm (eqm (to x13) (V 1))& (bacc (pk 3) (b 0 7) (r 8) (pi2 x12)) (qa121 )
                                    (ifm (eqm (to x13) (V 2))& (bacc (pk 3) (b 1 11) (r 12) (pi2 x12)) (qa122 )
                                                    (ifm (achecks x13) (qa123 ) O))).
 
Definition qa13_s := (ifm (eqm (to x13) (V 1))& (bacc (pk 3) (b 0 7) (r 8) (pi2 x12)) (qa131 )
                                    (ifm  (eqm (to x13) (V 2)) (qa132 ) O)).


Definition qa21_s := (ifm  (eqm (to x13) (V 1))  (qa211 )
                                   (ifm (achecks x13) (qa212 ) O)).

Definition qa22_s  := (ifm (eqm (to x13) (V 1))& (bacc (pk 3) (b 0 13) (r 14) (pi1 x12)) (qa221 )
                                    (ifm (eqm (to x13) (V 2))& (bacc (pk 3) (b 1 9) (r 10) (pi2 x12)) (qa222 )
                                                   (ifm (achecks x13) (qa223 ) O))).
 
Definition qa23_s := (ifm (eqm (to x13) (V 2))& (bacc (pk 3) (b 1 9) (r 10) (pi2 x12)) (qa231 )
                        (ifm  (eqm (to x13) (V 1))  (qa232 ) O)).

 
Definition qa31_s := (ifm (eqm (to x13) (V 1))& (bacc (pk 3) (b 0 15) (r 16) (pi1 x12)) (qa311 )
                                    (ifm  (eqm (to x13) (V 2))  (qa312 ) O)).

Definition qa32_s := (ifm (eqm (to x13) (V 2))& (bacc (pk 3) (b 1 17) (r 18) (pi2 x12)) (qa321 )
                                    (ifm  (eqm (to x13) (V 1)) (qa322 ) O)).
(********************************************************************************************)

Definition qa1_ss := (ifm (eqm (to x12) (V 1))& (bacc (pk 3) (b 0 7) (r 8) (pi1 x12))  (qa11_s )
			           (ifm (eqm (to x12) (V 2))  (qa12_s )
                                                  (ifm (achecks x12) (qa13_s ) O))).
 
Definition qa2_ss :=  (ifm (eqm (to x12) (V 2))& (bacc (pk 3) (b 1 9) (r 10) (pi2 x12))  (qa21_s )
			           (ifm (eqm (to x12) (V 1))  (qa22_s )
                                                   (ifm (achecks x12) (qa23_s ) O))).
 
Definition qa3_ss := (ifm (eqm (to x12) (V 1)) (qa31_s )
		    	            (ifm  (eqm (to x12) (V 2))  (qa32_s ) O)).


Definition t13 :=  (ifm (eqm (to x11) (V 1)) (qa1_ss )
		    	           (ifm (eqm (to x11) (V 2))  (qa2_ss )
                                                   (ifm (achecks x11) (qa3_ss )
                                                                   O))).

Definition phi14 := (phi13 ) ++ [msg (t13 )] .

(** * Frame [phi5] *)
 
Definition mphi4 := (conv_mylist_listm (phi14 )).
Definition x15 := (f (mphi4 )).
(**********************************************************)
Definition qa1111 := (admin x15).
 
Definition qa1112 :=  (ifm (eqm (to x15) (V 2))& (bacc (pk 3) (b 1 19) (r 20) (pi2 x12)) ok O).

(************************************************)
 
Definition qa1121 :=  (ifm (eqm (to x15) (V 2))& (bacc (pk 3) (b 1 31) (r 32) (pi2 x12)) ok O).

(************************************)

Definition qa1211 := (admin x15).

Definition qa1212 :=  (ifm (eqm (to x15) (V 2))& (bacc (pk 3) (b 1 11) (r 12) (pi2 x12)) ok O).

(***************************************)

Definition qa1221 := (admin x15).
Definition qa1222 :=  (ifm (eqm (to x15) (V 1))& (bacc (pk 3) (b 0 7) (r 8) (pi1 x12)) ok O).

(***************************************)

Definition qa1231 := (ifm (eqm (to x15) (V 2))& (bacc (pk 3) (b 1 11) (r 12) (pi2 x12)) ok O).
Definition qa1232 := (ifm (eqm (to x15) (V 1))& (bacc (pk 3) (b 0 7) (r 8) (pi1 x12)) ok O).

(***************************************)

Definition qa1311 := (ifm (eqm (to x15) (V 2))& (bacc (pk 3) (b 1 33) (r 34) (pi2 x12)) ok O).
(********************************)
Definition qa1321  := (ifm (eqm (to x15) (V 2))& (bacc (pk 3) (b 1 21) (r 22) (pi2 x12)) ok O). 
 
Definition qa1322 := (ifm (eqm (to x15) (V 1))& (bacc (pk 3) (b 0 7) (r 8) (pi1 x12)) ok O).

(*********************************)

Definition qa2111 :=  (admin x15).
Definition qa2112 := (ifm (eqm (to x15) (V 1))& (bacc (pk 3) (b 0 23) (r 24) (pi1 x12)) ok O).
(*******************************)
 
Definition qa2121 :=  (ifm (eqm (to x15) (V 1))& (bacc (pk 3) (b 0 35) (r 36) (pi1 x12)) ok O).

(*******************************)

Definition qa2211 := (admin x15).

Definition qa2212 :=   (ifm (eqm (to x15) (V 2))& (bacc (pk 3) (b 1 9) (r 10) (pi2 x12)) ok O).

(*******************************)

Definition qa2221 := (admin x15).

Definition qa2222 := (ifm (eqm (to x15) (V 1))& (bacc (pk 3) (b 0 13) (r 14) (pi1 x12)) ok O).
(******************************) 

Definition qa2231 :=  (ifm (eqm (to x15) (V 2))& (bacc (pk 3) (b 1 9) (r 10) (pi2 x12)) ok O).
Definition qa2232 := (ifm (eqm (to x15) (V 1))& (bacc (pk 3) (b 0 13) (r 14) (pi1 x12)) ok O).

(***********************************)

Definition qa2311 := (ifm (eqm (to x15) (V 1))& (bacc (pk 3) (b 0 37) (r 38) (pi1 x12)) ok O).

(**************************************)
 
Definition qa2321 :=  (ifm (eqm (to x15) (V 2))& (bacc (pk 3) (b 1 9) (r 10) (pi2 x12)) ok O).

Definition qa2322 := (ifm (eqm (to x15) (V 1))& (bacc (pk 3) (b 0 25) (r 26) (pi1 x12)) ok O).

(****************************************)

Definition qa3111 := (ifm (eqm (to x15) (V 2))& (bacc (pk 3) (b 0 39) (r 40) (pi2 x12)) ok O).

(*****************************************)

Definition qa3121  :=  (ifm (eqm (to x15) (V 2))& (bacc (pk 3) (b 1 27) (r 28) (pi2 x12)) ok O).
Definition qa3122 := (ifm (eqm (to x15) (V 1))& (bacc (pk 3) (b 0 15) (r 16) (pi1 x12)) ok O).
(**************************************)

Definition qa3222 := (ifm (eqm (to x15) (V 1))& (bacc (pk 3) (b 0 29) (r 30) (pi1 x12)) ok O).
Definition qa3221 :=  (ifm (eqm (to x15) (V 2))& (bacc (pk 3) (b 1 17) (r 18) (pi2 x12)) ok O).

(**************************************)

Definition qa3211 := (ifm (eqm (to x15) (V 1))& (bacc (pk 3) (b 0 41) (r 42) (pi1 x12)) ok O).


(************************************************************************)
(************************************************************************)


Definition qa111_s := (ifm  (eqm (to x14) (V 2))& (bacc (pk 3) (b 1 19) (r 20) (pi2 x12)) (qa1111 )
                                      (ifm (achecks x14) (qa1112 ) O)).
 
Definition qa112_s := (ifm  (eqm (to x14) (V 2)) (qa1121 ) O).
 
 (*************************************************)                       

  
Definition qa121_s := (ifm (eqm (to x14) (V 2 ))& (bacc (pk 3) (b 1 11) (r 12) (pi2 x12)) (qa1211 )
                        (ifm (achecks x14) (qa1212 ) O)).

Definition qa122_s := (ifm (eqm (to x14) (V 1 ))& (bacc (pk 3) (b 0 7) (r 8) (pi1 x12)) (qa1221 )
                          (ifm (achecks x14) (qa1222 ) O)).
 
Definition  qa123_s := (ifm (eqm (to x14) (V 1 ))& (bacc (pk 3) (b 0 7) (r 8) (pi1 x12)) (qa1231 )
                          (ifm (eqm (to x14) (V 2 ))& (bacc (pk 3) (b 0 11) (r 12) (pi2 x12)) (qa1232 )
                               O)).
(****************************************************)

Definition qa131_s := (ifm  (eqm (to x14) (V 2))  (qa1311 ) O).
 
Definition qa132_s :=  (ifm (eqm (to x14) (V 1 ))& (bacc (pk 3) (b 0 7) (r 8) (pi1 x12)) (qa1321 )
                          (ifm (eqm (to x14) (V 2 ))& (bacc (pk 3) (b 1 21) (r 22) (pi2 x12)) (qa1322 )
                               O)).
(****************************************************)
 
Definition qa211_s :=  (ifm (eqm (to x14) (V 1 ))& (bacc (pk 3) (b 0 23) (r 24) (pi1 x12)) (qa2111 )
                         (ifm (achecks x14) (qa2112 ) O)).

Definition qa212_s :=  (ifm  (eqm (to x14) (V 2))  (qa2121 ) O).


(***************************************************)

Definition qa221_s :=   (ifm (eqm (to x14) (V 2 ))& (bacc (pk 3) (b 1 9) (r 10) (pi2 x12)) (qa2211 )
                          (ifm (achecks x14) (qa2212 ) O)).
Definition qa222_s :=  (ifm (eqm (to x14) (V 1 ))& (bacc (pk 3) (b 0 13) (r 14) (pi1 x12)) (qa2221 )
                         (ifm (achecks x14) (qa2222 ) O)).
Definition qa223_s := (ifm (eqm (to x14) (V 1 ))& (bacc (pk 3) (b 0 13) (r 14) (pi1 x12)) (qa2231 )
                         (ifm (eqm (to x14) (V 2 ))& (bacc (pk 3) (b 1 9) (r 10) (pi2 x12)) (qa2232 )
                              O)).

(***************************************************)

Definition qa231_s := (ifm (eqm (to x14) (V 1)) (qa2311 ) O).
 
Definition qa232_s := (ifm (eqm (to x14) (V 1 ))& (bacc (pk 3) (b 0 25) (r 26) (pi1 x12)) (qa2321 )
                          (ifm (eqm (to x14) (V 2 ))& (bacc (pk 3) (b 1 9) (r 10) (pi2 x12)) (qa2322 )
                               O)).
(***************************************************)

Definition qa311_s := (ifm  (eqm (to x14) (V 2)) (qa3111 ) O).
Definition qa312_s :=  (ifm (eqm (to x14) (V 1 ))& (bacc (pk 3) (b 0 15) (r 16) (pi1 x12)) (qa3121 )
                          (ifm (eqm (to x14) (V 2 ))& (bacc (pk 3) (b 1 27) (r 28) (pi2 x12)) (qa3122 )
                               O)).

(****************************************)

Definition qa321_s := (ifm  (eqm (to x14) (V 1))  (qa3211 ) O).

Definition qa322_s :=  (ifm (eqm (to x14) (V 1 ))& (bacc (pk 3) (b 0 29) (r 30) (pi1 x12)) (qa3221 )
                          (ifm (eqm (to x14) (V 2 ))& (bacc (pk 3) (b 1 17) (r 18) (pi2 x12)) (qa3222 )
                               O)).

(*****************************************)
  (****************************************************************************************************)
Definition qa11_ss :=  (ifm  (eqm (to x13) (V 2)) (qa111_s )
                                      (ifm (achecks x13) (qa112_s ) O)).
 
Definition qa12_ss := (ifm (eqm (to x13) (V 1))& (bacc (pk 3) (b 0 7) (r 8) (pi2 x12)) (qa121_s )
                                    (ifm (eqm (to x13) (V 2))& (bacc (pk 3) (b 1 11) (r 12) (pi2 x12)) (qa122_s )
                                                    (ifm (achecks x13) (qa123_s ) O))).
 
Definition qa13_ss := (ifm (eqm (to x13) (V 1))& (bacc (pk 3) (b 0 7) (r 8) (pi2 x12)) (qa131_s )
                                    (ifm  (eqm (to x13) (V 2)) (qa132_s ) O)).


Definition qa21_ss := (ifm  (eqm (to x13) (V 1))  (qa211_s )
                                   (ifm (achecks x13) (qa212_s ) O)).

Definition qa22_ss := (ifm (eqm (to x13) (V 1))& (bacc (pk 3) (b 0 13) (r 14) (pi1 x12)) (qa221_s )
                                    (ifm (eqm (to x13) (V 2))& (bacc (pk 3) (b 1 9) (r 10) (pi2 x12)) (qa222_s )
                                                   (ifm (achecks x13) (qa223_s ) O))).
 
Definition qa23_ss := (ifm (eqm (to x13) (V 2))& (bacc (pk 3) (b 1 9) (r 10) (pi2 x12)) (qa231_s )
                        (ifm  (eqm (to x13) (V 1))  (qa232_s ) O)).

 
Definition qa31_ss := (ifm (eqm (to x13) (V 1))& (bacc (pk 3) (b 0 15) (r 16) (pi1 x12)) (qa311_s )
                                    (ifm  (eqm (to x13) (V 2))  (qa312_s ) O)).

Definition qa32_ss := (ifm (eqm (to x13) (V 2))& (bacc (pk 3) (b 1 17) (r 18) (pi2 x12)) (qa321_s )
                                    (ifm  (eqm (to x13) (V 1)) (qa322_s ) O)).
(********************************************************************************************)

Definition qa1_sss := (ifm (eqm (to x12) (V 1))& (bacc (pk 3) (b 0 7) (r 8) (pi1 x12))  (qa11_ss )
			           (ifm (eqm (to x12) (V 2))  (qa12_ss )
                                                  (ifm (achecks x12) (qa13_ss ) O))).
 
Definition qa2_sss :=  (ifm (eqm (to x12) (V 2))& (bacc (pk 3) (b 1 9) (r 10) (pi2 x12))  (qa21_ss )
			           (ifm (eqm (to x12) (V 1)) (qa22_ss )
                                                   (ifm (achecks x12) (qa23_ss ) O))).
 
Definition qa3_sss := (ifm (eqm (to x12) (V 1)) (qa31_ss )
		    	            (ifm  (eqm (to x12) (V 2))  (qa32_ss ) O)).


Definition t14 :=  (ifm (eqm (to x11) (V 1)) (qa1_sss )
		    	           (ifm (eqm (to x11) (V 2))  (qa2_sss )
                                                   (ifm (achecks x11) (qa3_sss )
                                                                   O))).

Definition phi15 := (phi14 ) ++ [msg (t14 )] .

(** protocol-2 **)
(*************************************************************************************************)


Definition qb0 :=  (ifm (eqm (to x1) (V 1)) ((pk 1), ((e (b 0 7) 8) , (sign (sk 1) (e (b 0 7) 8))))
		    	            (ifm  (eqm (to x1) (V 2))  ((pk 2), ( (e (b 1 9) 10),  (sign (sk 2) (e (b 1 9) 10))))
                                                 (admin x1)   )).
                                                                 

(** Vote Privacy 


     The two protocols, one in which Voter1 votes for A and Voter2 votes for B is indistinguishable from the one in which Voter1 votes for B and Voter2 votes for A.
*)
 (** Tactics *)

(*Ltac unf_mph := try unfold mphi110, mphi11, mphi2, mphi13, mphi20, mphi21, mphi22, mphi23.*)
 
Ltac unf_phi := try unfold phi0, phi11, phi12, phi13, phi14,  phi15.
 
Ltac unf_q :=  try unfold qa0, qa1, qa2, qa3; try unfold qa11, qa12, qa13;  try unfold qa21, qa22, qa23;  try unfold qa31, qa32; try unfold qa1_s, qa2_s, qa3_s;  try unfold qa111, qa112;
                try unfold qa121, qa122, qa123; try unfold qa131, qa132; try unfold qa211, qa212; try unfold qa221, qa222, qa223; try unfold qa231, qa232; try unfold qa311, qa312; try unfold qa321, qa322;   try unfold qa11_s, qa12_s, qa13_s;  try unfold qa21_s, qa22_s, qa23_s;  try unfold qa31_s, qa32_s; try unfold qa1_ss, qa2_ss, qa3_ss; try unfold qa1111, qa1112, qa1121, qa1211, qa1212, qa1221, qa1222, qa1231, qa1232, qa1311, qa1321, qa1322, qa2111, qa2112, qa2121, qa2211, qa2212, qa2221, qa2222, qa2231, qa2232, qa2311, qa2321, qa2322, qa3111, qa3121, qa3122, qa3222, qa3221, qa3211;
                 try unfold qa111_s, qa112_s;
                try unfold qa121_s, qa122_s, qa123_s; try unfold qa131_s, qa132_s; try unfold qa211_s, qa212_s; try unfold qa221_s, qa222_s, qa223_s; try unfold qa231_s, qa232_s; try unfold qa311_s, qa312_s; try unfold qa321_s, qa322_s;  try unfold qa11_ss, qa12_ss, qa13_ss;  try unfold qa21_ss, qa22_ss, qa23_ss;  try unfold qa31_ss, qa32_ss; try unfold qa1_sss, qa2_sss, qa3_sss.

Ltac unf_trm:=  try unfold t11, t2, t3, t4.

Ltac unf := try unf_phi; try unf_trm; try unf_q.


(** * Axioms and Definitions *)
Ltac funappmconst t H := apply FUNCApp_mconst with (m:= t) in H; simpl in H.

Ltac funappbconst b1 H := apply FUNCApp_bconst with (b:= b1) in H; simpl in H.

Ltac funappf1 f n H:= apply FUNCApp_f1 with (f1:= f) (p:= n) in H; simpl in H.

Ltac funappf2mb f H:= apply FUNCApp_f2b with (f2b:= f) (p1:= 0) (p2:= 1) in H; simpl in H.

Ltac funappf2m f H:= apply FUNCApp_f2m with (f2m:= f) (p1:= 0) (p2:= 1) in H; simpl in H.

Ltac funappf3mb f n3 H:= apply FUNCApp_f3b with (f3b:= f) (p1:= 0) (p2:= 1) (p3:= n3) in H; simpl in H.

Ltac funappf3m f n3 H:= apply FUNCApp_f3m with (f3m:= f) (p1:= 0) (p2:= 1) (p3:= n3) in H; simpl in H.

Ltac funappifm  n3 H:= apply FUNCApp_f3bm with (f3bm:= ifm) (p1:= 0) (p2:= 1) (p3:= n3) in H; simpl in H.

Ltac funappifb  n3 H:= apply FUNCApp_g3 with (g3:= ifb) (p1:= 0) (p2:= 1) (p3:= n3) in H; simpl in H.

Ltac funappf2b f H:= apply FUNCApp_f1 with (g2:= f ) (p1 := 0 ) (p2:= 1) in H; simpl in H.

Ltac retmylis H :=
  match goal with
    |[H: ?X ~ _  |- _ ] => pose (l := x1)
  end.
Fixpoint eltPos  (x:oursum) {n} (l:mylist n) :nat :=
  match l with
    | [] => 0
    | h::t =>  if  (oursum_beq x1 h)  then 1 else S (eltPos x1 t)
  end.


Ltac funappeltPos2 tac f x1 y l H :=  retmylis H; tac f (eltPos x1 l) (eltPos y l) H; clear l.



Ltac funappeltPos3 tac x1 y z l H :=  tac  (eltPos x1 l) (eltPos y l) (eltPos z l) H; clear l.
 
Ltac aplyProjList l H1 :=
  match l with
    | [] => idtac
    | ?h :: ?t =>  simpl in H1; apply RESTR_proj with (p:= h) in H1; try reflexivity; unfold proj_at_pos in H1; simpl in H1; 
                    aplyProjList t H1; try reflexivity
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

 
 Axiom restr_sublis : forall {m} {n} (l1 l2 : mylist m) (l1' l2': mylist n) ,  l1 ~ l2 -> (andb (checksublis l1' l1) (checksublis l2' l2)  = true ) -> (sublisIndcs l1' l1) = (sublisIndcs l2' l2)-> l1' ~ l2'.

 Ltac restrsublis H :=
   match goal with
     | [|- ?X ~ ?Y] => apply restr_sublis with (l1':= x1) (l2':=Y) in H; simpl in H; try assumption; try reflexivity
   end.

Definition topsymsg_beq (t t': message ) : bool :=
   match t, t' with
     | ifm  _ _ _ , ifm _ _ _ => true
     | ifm  _ _ _ , _ => false
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
     | eqb  _ _ , eqb _ _  =>  true
     | eqm _ _, eqm _ _ =>  true
     | ifb _ _ _, ifb _ _ _ => true
     | EQL _ _ , EQL _ _ => true
     | ver _ _ _, ver _ _ _ => true
     | bver _ _ _, bver _ _ _ => true
     | bacc _ _ _ _, bacc _ _ _ _  =>true
     | Bvar _,  _ =>  false
     | eqb  _ _ , _  =>  false
     | eqm _ _,   _ =>  false
     | ifb _ _ _,  _ => false
     | EQL _ _ , _ => false
     | ver _ _ _,  _ => false
     | bver _ _ _, _ => false
     | bacc _ _ _ _, _  =>false
     | _ , _ => Bool_beq b b'
   end.
 Eval compute in topsymsg_beq (ifm _ _ _) O.

Definition topsyos_beq (t11 t2 : oursum): bool :=
  match t11 , t2 with
      | msg t11', msg t2' => topsymsg_beq t11' t2'
      | bol b1, bol b2 => topsybol_beq b1 b2
      | _ , _ => false
  end.
            
           
 
(** * Assumptions *)
(** blinds of two indistinguishable messages are also indistinguishable *)
(** Signatures of two indistinguishable messages are also indistinguishable *)
 
 
Fixpoint checkostmylis (x:oursum) {n} (l:mylist n) : bool :=
  match l with
    | [] => false
    | h :: t => if (oursum_beq x1 h) then true else (checkostmylis x1 t)
  end.

(** checksublis: mylist m -> mylist n -> bool *)
Fixpoint checksublis'  (l: list oursum) {n} (l':mylist n) : bool :=
match (leb n n) , l with
  | true , nil => true
  | true , cons h t => if (checkostmylis h  l') then (checksublis' t l')
                     else false
  | _ , _ => false
end.

(** sublisIndcs: mylist m -> mylist n -> list nat *)
                    
 Fixpoint  sublisIndcs'  {n} (l :list oursum) (l': mylist n) : list nat :=
  match  l with
    | nil => nil
    | cons h t => cons (eltPos h l')  (sublisIndcs' t l')
  end.


(** Tactics *)

(** Projection n times *)
Ltac aplyprojn n n' H:=
  match n with
    | 0 => idtac
    | S ?n'' => aplyProjList  [n'] H; simpl in H; aplyprojn n'' n' H; try reflexivity
  end.

Section subtrm'.
Variable f: message -> list oursum.
Fixpoint mapsubtrmls (l: list message) : list oursum :=
  match l with
    | nil => nil
    | cons h t => (app (f h) (mapsubtrmls t))
  end.
End subtrm'.
Fixpoint subtrmls_bol'(t: Bool) : list oursum :=
  match t with 
    | eqb  b1 b2 =>  (app (subtrmls_bol' b1) (subtrmls_bol' b2) )
    | eqm t11 t2 => (app (subtrmls_msg' t11) (subtrmls_msg' t2) )
    | ifb t11 t2 t3 => (app (subtrmls_bol' t11) (app (subtrmls_bol' t2) (subtrmls_bol' t3)))
    | EQL t11 t2 => (app (subtrmls_msg' t11) (subtrmls_msg' t2) )
    | ver t11 t2 t3 => (app (subtrmls_msg' t11) (app (subtrmls_msg' t2) (subtrmls_msg' t3)))
    | bver t11 t2 t3 => (app (subtrmls_msg' t11) (app (subtrmls_msg' t2) (subtrmls_msg' t3)))
    | bacc t11 t2 t3 t4 => (app (subtrmls_msg' t11) (app (subtrmls_msg' t2) (app (subtrmls_msg' t3) (subtrmls_msg' t4))))
    | _ => nil
 end
with subtrmls_msg' (t:message) : list oursum :=
       match t with 
         | ifm b3 t11 t2 => (app (subtrmls_bol' b3) (app (subtrmls_msg' t11) (subtrmls_msg' t2))) 
         | (Mvar n') => (cons (msg (Mvar n')) nil)
         | acc => (cons (msg acc) nil)
         | lnc => (cons (msg lnc) nil)
         | lsk => (cons (msg lsk) nil)
         | O => (cons (msg O) nil)
         | N n'=> (cons (msg (N n')) nil)
         | new =>  (cons (msg new) nil)
         | exp t11 t2 t3 => (app (subtrmls_msg' t11) (app (subtrmls_msg' t2) (subtrmls_msg' t3)))
         | pair t11 t2 =>  (app (subtrmls_msg'  t11) (subtrmls_msg' t2) )
         | pi1 t11 => match t11 with
                       | k _ => (cons (msg (pi1 t11)) nil)
                       | _ => nil
                     end
         | pi2 t11 => match t11 with
                       | k _ => (cons (msg (pi2 t11)) nil)
                       | _ => nil
                     end
         | ggen t11 =>  (subtrmls_msg' t11)
         | act t11 =>  (subtrmls_msg' t11)
         | rr t11 =>  (subtrmls_msg' t11) 
         | rs t11 =>  (subtrmls_msg' t11) 
         | L t11 =>  (subtrmls_msg' t11) 
         | m t11 =>  (subtrmls_msg' t11) 
         | enc t11 t2 t3 => (app (subtrmls_msg' t11) (app (subtrmls_msg' t2) (subtrmls_msg' t3)))
         | dec t11 t2 =>  (app (subtrmls_msg' t11) (subtrmls_msg' t2))
         | k t11 =>  (subtrmls_msg' t11) 
         | nc n => (cons (msg (nc n)) nil) 
         | to t11 =>  (subtrmls_msg' t11) 
         | reveal t11 =>  (subtrmls_msg' t11) 
         | sign t11 t2 =>   (app (subtrmls_msg' t11) (subtrmls_msg' t2))
         (** Foo function protocol *)
         | commit t11 t2 t3 =>  (cons (msg t) nil)
         | open t11 t2 t3 =>  (app (subtrmls_msg' t11) (app (subtrmls_msg' t2) (subtrmls_msg' t3))) 
         | blind t11 t2 t3 =>  (cons (msg t) nil)
         | unblind t11 t2 t3 t4 =>  (app (subtrmls_msg' t11) (app (subtrmls_msg' t2) (app (subtrmls_msg' t3) (subtrmls_msg' t4))))
         | v t11 => (cons (msg (v t11)) nil)
         | V n => (cons (msg (V n)) nil)
         | ok => (cons (msg ok) nil)
         | bsign t11 t2 =>   (app (subtrmls_msg' t11) (subtrmls_msg' t2))
         | f l =>  (@mapsubtrmls subtrmls_msg' l)
         | _ => nil
       end.


(** Subterms of [oursum] term. *)

Definition subtrmls_os' (t:oursum) : list oursum :=
  match t with 
    | msg t11 => subtrmls_msg' t11
    | bol b1 =>  subtrmls_bol' b1
  end.

(** Subterms of terms of type [mylist n] for some [n].*)

Fixpoint subtrmls_mylis' {n} (l:mylist n) : list oursum :=
  match l with 
    | [] => nil
    | h:: t => (app (subtrmls_os' h) (subtrmls_mylis' t))
  end.
  
 


Axiom funapptrm : forall {m} (t11 t2 : oursum) (l1 l2 : mylist m),  l1 ~ l2 -> (topsyos_beq t11 t2 = true ) -> (andb (checksublis' (subtrmls_os' t11)  l1) (checksublis' (subtrmls_os' t2) l2) = true) ->  (sublisIndcs' (subtrmls_os' t11) l1) = (sublisIndcs' (subtrmls_os' t2) l2) -> (l1 ++ [ t11]) ~ (l2 ++ [ t2]).

Ltac funapptrmhyp m1 m2 H := 
  apply funapptrm with (t11 := m1) (t2 := m2) in H; simpl in H; try reflexivity.
 
 (** blindness *) 
Ltac aply_blindnes n n3 n4 m0 m1 t11 t2 t3 t4 l H H0  := pose proof( blindness n n3 n4 m0 m1 t11 t2 t3 t4 l ) as H ;
assert( H0:  (Fresh [0; 1; n3; n4] (l++[ msg (N n); msg m0; msg m1]) = true) /\ (check_rn_blind_listm [0;1;n3;n4] [t11;t2;t3;t4] = true)); try split; try reflexivity;
apply H0 in H; clear H; simpl in H.

(** Using [funapptrmhyp] *)
Ltac appconst H:=
  funappmconst ok H; funappmconst (V 1) H; funappmconst (V 2) H; funappmconst O H; try reflexivity.
 
 Ltac x11checks H := funapptrmhyp (msg x11) (msg x11) H ;
                   funapptrmhyp (msg (to x11)) (msg (to x11)) H; 
                   funapptrmhyp (bol (eqm (to x11) (V 1))) (bol (eqm (to x11) (V 1))) H;
                   funapptrmhyp (bol (eqm (to x11) (V 2))) (bol (eqm (to x11) (V 2))) H; 
                   funapptrmhyp (bol (eqm (to x11) (pk 3))) (bol (eqm (to x11) (pk 3))) H.
  
Axiom fresh_blind : forall (0 1 n3 n4 n5 n6 n7 : nat) {n} (l1 l2 :mylist n),
                      (l1 ++ [msg (e (b ) n3)]) ~ (l2 ++ [msg (e (b n4 n5) n6)]) ->  Fresh [n7] (l1 ++ [msg (e (b ) n3)] ++  l2 ++ [msg (e (b n4 n5) n6)]) = true  -> (l1 ++ [msg (e (b ) n7)])  ~ (l2 ++ [msg (e (b n4 n5) n7)]).
Axiom fresh_commit : forall (0 1 n3 n4 n5 n6 n7 : nat) {n} (l1 l2 :mylist n), Fresh [n7] (l1++ [msg (e (b ) n3)] ++  l2 ++ [msg (e (b n4 n5) n6)]) = true ->
                      (l1 ++ [msg (e (b ) n3)]) ~ (l2 ++ [msg (e (b n4 n5) n6)]) -> (l1 ++ [msg (e (b 0 n7) n3)]) ~ (l2 ++ [msg (e (b n4 n7) n6)]). 
  
 Ltac adminchecks t11 t2 H:=
  funapptrmhyp (msg (pi1 t11)) (msg (pi1 t2)) H;
  funapptrmhyp (msg (pi1 (pi1 t11))) (msg (pi1 (pi1 t2))) H;
  funapptrmhyp (msg (pi2 (pi1 t11))) (msg (pi2 (pi1 t2))) H;
  funapptrmhyp (msg (pi1 (pi2 (pi1 t11)))) (msg (pi1 (pi2 (pi1 t2)))) H;
  funapptrmhyp (msg (pi2 (pi2 (pi1 t11)))) (msg (pi2 (pi2 (pi1 t2)))) H;
  funapptrmhyp (msg (pi2 t11)) (msg (pi2 t2)) H;
  funapptrmhyp (msg (pi1 (pi2 t11))) (msg (pi1 (pi2 t2))) H;
  funapptrmhyp (msg (pi2 (pi2 t11))) (msg (pi2 (pi2 t2))) H;
  funapptrmhyp (msg (pi1 (pi2 (pi2 t11)))) (msg (pi1 (pi2 (pi2 t2)))) H;
  funapptrmhyp (msg (pi2 (pi2 (pi2 t11)))) (msg (pi2 (pi2 (pi2 t2)))) H;
  funapptrmhyp (msg (bsign (sk 3) (pi1 (pi2 (pi1 t11))) )) (msg (bsign (sk 3) (pi1 (pi2 (pi1 t2))) )) H;
  funapptrmhyp (msg (bsign (sk 3) (pi1 (pi2 (pi2 t11))) )) (msg (bsign (sk 3) (pi1 (pi2 (pi2 t2))) )) H;
  funapptrmhyp (msg ((bsign (sk 3) (pi1 (pi2 (pi1 t11))) ) , (bsign (sk 3) (pi1 (pi2 (pi2 t2))) ))) (msg ((bsign (sk 3) (pi1 (pi2 (pi1 t11))) ), (bsign (sk 3) (pi1 (pi2 (pi2 t12))) ))) H;
 funapptrmhyp (bol (ver (pi1 (pi1 x11))  (pi1 (pi2 (pi1 x11))) (pi2 (pi2 (pi1 x11))))) (bol (ver (pi1 (pi1 x11))  (pi1 (pi2 (pi1 x11))) (pi2 (pi2 (pi1 x11))))) H;
 funapptrmhyp (bol (ver (pi1 (pi2 x11))  (pi1 (pi2 (pi2 x11))) (pi2 (pi2 (pi2 x11)))))  (bol (ver (pi1 (pi2 x11))  (pi1 (pi2 (pi2 x11))) (pi2 (pi2 (pi2 x11))))) H.

 
Theorem frame2Ind:  (phi11 0 1 )~ (phi11 1 0).
Proof. repeat unf.
       simpl.
apply IFBRANCH_M1 with (ml1:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5)]) (ml2:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5)]).
simpl. 
   
pose proof(blindness 3 8 9 0 1 (b 0 7) (b 1 7) ((Mvar 0), (Mvar 1)) ((Mvar 0), (Mvar 1))  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                                                           msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2) ] ).
simpl in H. 
 
aplyprojn 2 14 H ;try split; try reflexivity.
appconst H.
 x11checks H.
 funapptrmhyp (msg (sign (sk 1) (e (b 0 7) 8)))  (msg (sign (sk 1) (e (b 1 7) 8))) H.
 funapptrmhyp (msg ((e (b 0 7) 8), (sign (sk 1) (e (b 0 7) 8))))  (msg ((e (b 1 7) 8), (sign (sk 1) (e (b 1 7) 8)))) H.
  funapptrmhyp (msg ((pk 1), ((e (b 0 7) 8), (sign (sk 1) (e (b 0 7) 8)))))  (msg ((pk 1), ((e (b 1 7) 8), (sign (sk 1) (e (b 1 7) 8))))) H.
 restrsublis H.
 (** subgoal-II *)

 simpl.
apply IFBRANCH_M1 with (ml1:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); bol (eqm (to x11) (V 1))]) (ml2:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); bol (eqm (to x11) (V 1))]).
simpl.

pose proof(blindness 3 10 11 0 1 (b 1 9) (b 0 9) ((Mvar 0), (Mvar 1)) ((Mvar 0), (Mvar 1))  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                                                           msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2) ] ).
simpl in H. 
 
aplyprojn 2 14 H ;try split; try reflexivity.
appconst H.
 x11checks H.
 funapptrmhyp (msg (sign (sk 2) (e (b 1 9) 10)))  (msg (sign (sk 2) (e (b 0 9) 10))) H. 
 funapptrmhyp  (msg ((e (b 1 9) 10), (sign (sk 2) (e (b 1 9) 10))))  (msg ((e (b 0 9) 10), (sign (sk 2) (e (b 0 9) 10)))) H.
 funapptrmhyp  (msg (pk 2, ((e (b 1 9) 10), (sign (sk 2) (e (b 1 9) 10)))))  (msg (pk 2, ((e (b 0 9) 10), (sign (sk 2) (e (b 0 9) 10))))) H. 
 restrsublis H. reflexivity.
Qed.
  
Theorem frame3Ind: (phi12 ) ~ (phi12 1 0).
  Proof. repeat unf.
         simpl.
         apply IFBRANCH_M2 with (ml1:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); msg (pk 5)]) (ml2 := [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); msg (pk 5)]).
         simpl.
apply IFBRANCH_M1 with (ml1:=      [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); bol (eqm (to x11) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8)))]) (ml2:=    [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); bol (eqm (to x11) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (e (b 1 7) 8)))]).
simpl. 
(** Subgoal-I *)
 


 pose proof(blindness 3 8 10 0 1 (b 0 7) (b 1 9) ((Mvar 0), (Mvar 1)) ((Mvar 0), (Mvar 1))  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                                                           msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2) ] ).
simpl in H. 
 aplyprojn 1 14 H ;try split; try reflexivity.
appconst H.
 x11checks H.  
 funapptrmhyp (msg (sign (sk 1) (e (b 0 7) 8)))  (msg (sign (sk 1) (e (b 1 7) 8))) H; simpl; try reflexivity.
 funapptrmhyp (msg ((e (b 0 7) 8), (sign (sk 1) (e (b 0 7) 8))))  (msg ((e (b 1 7) 8), (sign (sk 1) (e (b 1 7) 8)))) H.
 funapptrmhyp (msg ((pk 1), ((e (b 0 7) 8), (sign (sk 1) (e (b 0 7) 8)))))  (msg ((pk 1), ((e (b 1 7) 8), (sign (sk 1) (e (b 1 7) 8))))) H. 
 
 funapptrmhyp (msg x12) (msg (x2 1 0)) H
funapptrmh
 restrsublis H.



(** Subgoal-II *)
Focus 2. 
 simpl.
apply IFBRANCH_M1 with (ml1:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); bol (eqm (to x11) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8)));
    bol
      (eqm (to x12) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 x12))]) (ml2:=  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); bol (eqm (to x11) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (e (b 1 7) 8)));
   bol (eqm (to (x2 1 0)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2 1 0)))]). simpl.



pose proof(blindness 3 8 10 0 1 (b 0 7) (b 1 7) ((Mvar 0), (Mvar 1)) ((Mvar 0), (Mvar 1))  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                                                           msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2) ;msg (sk 3)] ).
simpl in H.
aplyprojn 1 15 H ;try split; try reflexivity.  
pose proof (fresh_commit 
1 7 10 0 7 10 9 [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
       msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2);  msg (sk 3);
       msg (N 3); msg (b 0 7); msg (b 1 7); msg (blind (b 0 7) (pk 3) (r 8))] [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
      msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); msg (sk 3);
      msg (N 3); msg (b 0 7); msg (b 1 7); msg (blind (b 1 7) (pk 3) (r 8))]).  simpl in H0. 
apply H0 in H;try reflexivity. clear H0.
appconst H.
x1checks H.
 funapptrmhyp (msg (sign (sk 1) (e (b 0 7) 8)))  (msg (sign (sk 1) (e (b 1 7) 8))) H.
 funapptrmhyp (msg ((e (b 0 7) 8), (sign (sk 1) (e (b 0 7) 8))))  (msg ((e (b 1 7) 8), (sign (sk 1) (e (b 1 7) 8)))) H.
 funapptrmhyp (msg ((pk 1), ((e (b 0 7) 8), (sign (sk 1) (e (b 0 7) 8)))))  (msg ((pk 1), ((e (b 1 7) 8), (sign (sk 1) (e (b 1 7) 8))))) H.
  funapptrmhyp (msg (sign (sk 2) (e (b 1 9) 10)))  (msg (sign (sk 2) (e (b 0 9) 10))) H. 
 funapptrmhyp  (msg ((e (b 1 9) 10), (sign (sk 2) (e (b 1 9) 10))))  (msg ((e (b 0 9) 10), (sign (sk 2) (e (b 0 9) 10)))) H.
 funapptrmhyp  (msg (pk 2, ((e (b 1 9) 10), (sign (sk 2) (e (b 1 9) 10)))))  (msg (pk 2, ((e (b 0 9) 10), (sign (sk 2) (e (b 0 9) 10))))) H.

adminchecks x11 x11 H.
funapptrmhyp (msg (ifm  (eqm (to x11) (V 2))  ((pk 2), ( (e (b 1 9) 10),  (sign (sk 2) (e (b 1 9) 10))))
                                                 (admin x11)   )) (msg (ifm  (eqm (to x11) (V 2))  ((pk 2), ( (e (b 0 9) 10),  (sign (sk 2) (e (b 0 9) 10))))
                                                  (admin x11)   )) H.
funapptrmhyp (msg (q0 )) (msg (q0 1 0)) H.
funapptrmhyp (msg x12) (msg (x2 1 0)) H. 
funapptrmhyp (msg (to x12)) (msg (to (x2 1 0))) H. 
funapptrmhyp (bol (eqm (to x12) (V 1))) (bol (eqm (to (x2 1 0)) (V 1))) H.
Check H.
retmylis H.
reswap_in 14 49 H. 
clear l. 
apply fresh_commit with (l1:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
       msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); 
       msg (sk 3); msg (N 3); msg (b 0 7); msg (b 1 7);
       msg (blind (b 0 7) (pk 3) (r 8)); bol (eqm (to x12) (V 1));
       msg ok; msg (V 1); msg (V 2); msg O; msg x11; 
       msg (to x11); bol (eqm (to x11) (V 1)); bol (eqm (to x11) (V 2));
       bol (eqm (to x11) (pk 3)); msg (sign (sk 1) (e (b 0 7) 8));
       msg (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8));
       msg (pk 1, (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8)));
       msg (sign (sk 2) (e (b 1 9) 10));
       msg (e (b 1 9) 10, sign (sk 2) (e (b 1 9) 10));
       msg (pk 2, (e (b 1 9) 10, sign (sk 2) (e (b 1 9) 10))); 
       msg (pi1 x11); msg (pi1 (pi1 x11)); msg (pi2 (pi1 x11));
       msg (pi1 (pi2 (pi1 x11))); msg (pi2 (pi2 (pi1 x11))); 
       msg (pi2 x11); msg (pi1 (pi2 x11)); msg (pi2 (pi2 x11));
       msg (pi1 (pi2 (pi2 x11))); msg (pi2 (pi2 (pi2 x11)));
       msg (bsign (sk 3) (pi1 (pi2 (pi1 x11))));
       msg (bsign (sk 3) (pi1 (pi2 (pi2 x11))));
       msg
         (bsign (sk 3) (pi1 (pi2 (pi1 x11))),
         bsign (sk 3) (pi1 (pi2 (pi2 x11))));
       bol (ver (pi1 (pi1 x11)) (pi1 (pi2 (pi1 x11))) (pi2 (pi2 (pi1 x11))));
       bol (ver (pi1 (pi2 x11)) (pi1 (pi2 (pi2 x11))) (pi2 (pi2 (pi2 x11))));
       msg
         (ifm (eqm (to x11) (V 2))
            (pk 2, (e (b 1 9) 10, sign (sk 2) (e (b 1 9) 10))) 
            (admin x11)); msg (q0 ); msg x12; 
       msg (to x12)])  (0:=1) (1:= 9) (n3:= 10) (n4:= 0) (n5:= 9) (n6:= 10) (n7:=11) (l2:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
      msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); 
      msg (sk 3); msg (N 3); msg (b 0 7); msg (b 1 7);
      msg (blind (b 1 7) (pk 3) (r 8)); bol (eqm (to (x2 1 0)) (V 1));
      msg ok; msg (V 1); msg (V 2); msg O; msg x11; 
      msg (to x11); bol (eqm (to x11) (V 1)); bol (eqm (to x11) (V 2));
      bol (eqm (to x11) (pk 3)); msg (sign (sk 1) (e (b 1 7) 8));
      msg (e (b 1 7) 8, sign (sk 1) (e (b 1 7) 8));
      msg (pk 1, (e (b 1 7) 8, sign (sk 1) (e (b 1 7) 8)));
      msg (sign (sk 2) (e (b 0 9) 10));
      msg (e (b 0 9) 10, sign (sk 2) (e (b 0 9) 10));
      msg (pk 2, (e (b 0 9) 10, sign (sk 2) (e (b 0 9) 10))); 
      msg (pi1 x11); msg (pi1 (pi1 x11)); msg (pi2 (pi1 x11));
      msg (pi1 (pi2 (pi1 x11))); msg (pi2 (pi2 (pi1 x11))); 
      msg (pi2 x11); msg (pi1 (pi2 x11)); msg (pi2 (pi2 x11));
      msg (pi1 (pi2 (pi2 x11))); msg (pi2 (pi2 (pi2 x11)));
      msg (bsign (sk 3) (pi1 (pi2 (pi1 x11))));
      msg (bsign (sk 3) (pi1 (pi2 (pi2 x11))));
      msg
        (bsign (sk 3) (pi1 (pi2 (pi1 x11))),
        bsign (sk 3) (pi1 (pi2 (pi2 x11))));
      bol (ver (pi1 (pi1 x11)) (pi1 (pi2 (pi1 x11))) (pi2 (pi2 (pi1 x11))));
      bol (ver (pi1 (pi2 x11)) (pi1 (pi2 (pi2 x11))) (pi2 (pi2 (pi2 x11))));
      msg
        (ifm (eqm (to x11) (V 2))
           (pk 2, (e (b 0 9) 10, sign (sk 2) (e (b 0 9) 10))) 
           (admin x11)); msg (q0 1 0); msg (x2 1 0); 
      msg (to (x2 1 0))]) in H;try reflexivity; simpl in H. 
apply fresh_blind with (l1:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
       msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); 
       msg (sk 3); msg (N 3); msg (b 0 7); msg (b 1 7);
       msg (blind (b 0 7) (pk 3) (r 8)); bol (eqm (to x12) (V 1));
       msg ok; msg (V 1); msg (V 2); msg O; msg x11; 
       msg (to x11); bol (eqm (to x11) (V 1)); bol (eqm (to x11) (V 2));
       bol (eqm (to x11) (pk 3)); msg (sign (sk 1) (e (b 0 7) 8));
       msg (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8));
       msg (pk 1, (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8)));
       msg (sign (sk 2) (e (b 1 9) 10));
       msg (e (b 1 9) 10, sign (sk 2) (e (b 1 9) 10));
       msg (pk 2, (e (b 1 9) 10, sign (sk 2) (e (b 1 9) 10))); 
       msg (pi1 x11); msg (pi1 (pi1 x11)); msg (pi2 (pi1 x11));
       msg (pi1 (pi2 (pi1 x11))); msg (pi2 (pi2 (pi1 x11))); 
       msg (pi2 x11); msg (pi1 (pi2 x11)); msg (pi2 (pi2 x11));
       msg (pi1 (pi2 (pi2 x11))); msg (pi2 (pi2 (pi2 x11)));
       msg (bsign (sk 3) (pi1 (pi2 (pi1 x11))));
       msg (bsign (sk 3) (pi1 (pi2 (pi2 x11))));
       msg
         (bsign (sk 3) (pi1 (pi2 (pi1 x11))),
         bsign (sk 3) (pi1 (pi2 (pi2 x11))));
       bol (ver (pi1 (pi1 x11)) (pi1 (pi2 (pi1 x11))) (pi2 (pi2 (pi1 x11))));
       bol (ver (pi1 (pi2 x11)) (pi1 (pi2 (pi2 x11))) (pi2 (pi2 (pi2 x11))));
       msg
         (ifm (eqm (to x11) (V 2))
            (pk 2, (e (b 1 9) 10, sign (sk 2) (e (b 1 9) 10))) 
            (admin x11)); msg (q0 ); msg x12; 
       msg (to x12)])  (0:=1) (1:= 11) (n3:= 10) (n4:= 0) (n5:= 11) (n6:= 10) (n7:=12) (l2:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
      msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); 
      msg (sk 3); msg (N 3); msg (b 0 7); msg (b 1 7);
      msg (blind (b 1 7) (pk 3) (r 8)); bol (eqm (to (x2 1 0)) (V 1));
      msg ok; msg (V 1); msg (V 2); msg O; msg x11; 
      msg (to x11); bol (eqm (to x11) (V 1)); bol (eqm (to x11) (V 2));
      bol (eqm (to x11) (pk 3)); msg (sign (sk 1) (e (b 1 7) 8));
      msg (e (b 1 7) 8, sign (sk 1) (e (b 1 7) 8));
      msg (pk 1, (e (b 1 7) 8, sign (sk 1) (e (b 1 7) 8)));
      msg (sign (sk 2) (e (b 0 9) 10));
      msg (e (b 0 9) 10, sign (sk 2) (e (b 0 9) 10));
      msg (pk 2, (e (b 0 9) 10, sign (sk 2) (e (b 0 9) 10))); 
      msg (pi1 x11); msg (pi1 (pi1 x11)); msg (pi2 (pi1 x11));
      msg (pi1 (pi2 (pi1 x11))); msg (pi2 (pi2 (pi1 x11))); 
      msg (pi2 x11); msg (pi1 (pi2 x11)); msg (pi2 (pi2 x11));
      msg (pi1 (pi2 (pi2 x11))); msg (pi2 (pi2 (pi2 x11)));
      msg (bsign (sk 3) (pi1 (pi2 (pi1 x11))));
      msg (bsign (sk 3) (pi1 (pi2 (pi2 x11))));
      msg
        (bsign (sk 3) (pi1 (pi2 (pi1 x11))),
        bsign (sk 3) (pi1 (pi2 (pi2 x11))));
      bol (ver (pi1 (pi1 x11)) (pi1 (pi2 (pi1 x11))) (pi2 (pi2 (pi1 x11))));
      bol (ver (pi1 (pi2 x11)) (pi1 (pi2 (pi2 x11))) (pi2 (pi2 (pi2 x11))));
      msg
        (ifm (eqm (to x11) (V 2))
           (pk 2, (e (b 0 9) 10, sign (sk 2) (e (b 0 9) 10))) 
           (admin x11)); msg (q0 1 0); msg (x2 1 0); 
      msg (to (x2 1 0))]) in H;try reflexivity; simpl in H.
funapptrmhyp (msg (pi1 (x2 0 1 ))) (msg (pi1 (x2 1 0))) H.

restrsublis H.
(*** subgoal *)
simpl. 

pose proof(blindness 3 8 10 0 1 (b 0 7) (b 1 7) ((Mvar 0), (Mvar 1)) ((Mvar 0), (Mvar 1))  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                                                           msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2) ;msg (sk 3)] ).
simpl in H.
aplyprojn 1 15 H ;try split; try reflexivity.  
pose proof (fresh_commit 
1 7 10 0 7 10 9 [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
       msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2);  msg (sk 3);
       msg (N 3); msg (b 0 7); msg (b 1 7); msg (blind (b 0 7) (pk 3) (r 8))] [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
      msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); msg (sk 3);
      msg (N 3); msg (b 0 7); msg (b 1 7); msg (blind (b 1 7) (pk 3) (r 8))]).  simpl in H0. 
apply H0 in H;try reflexivity.
appconst H.
x1checks H. clear H0.
 funapptrmhyp (msg (sign (sk 1) (e (b 0 7) 8)))  (msg (sign (sk 1) (e (b 1 7) 8))) H.
 funapptrmhyp (msg ((e (b 0 7) 8), (sign (sk 1) (e (b 0 7) 8))))  (msg ((e (b 1 7) 8), (sign (sk 1) (e (b 1 7) 8)))) H.
 funapptrmhyp (msg ((pk 1), ((e (b 0 7) 8), (sign (sk 1) (e (b 0 7) 8)))))  (msg ((pk 1), ((e (b 1 7) 8), (sign (sk 1) (e (b 1 7) 8))))) H.
  funapptrmhyp (msg (sign (sk 2) (e (b 1 9) 10)))  (msg (sign (sk 2) (e (b 0 9) 10))) H. 
 funapptrmhyp  (msg ((e (b 1 9) 10), (sign (sk 2) (e (b 1 9) 10))))  (msg ((e (b 0 9) 10), (sign (sk 2) (e (b 0 9) 10)))) H.
 funapptrmhyp  (msg (pk 2, ((e (b 1 9) 10), (sign (sk 2) (e (b 1 9) 10)))))  (msg (pk 2, ((e (b 0 9) 10), (sign (sk 2) (e (b 0 9) 10))))) H.

adminchecks x11 x11 H.
funapptrmhyp (msg (ifm  (eqm (to x11) (V 2))  ((pk 2), ( (e (b 1 9) 10),  (sign (sk 2) (e (b 1 9) 10))))
                                                 (admin x11)   )) (msg (ifm  (eqm (to x11) (V 2))  ((pk 2), ( (e (b 0 9) 10),  (sign (sk 2) (e (b 0 9) 10))))
                                                  (admin x11)   )) H.
funapptrmhyp (msg (q0 )) (msg (q0 1 0)) H.
funapptrmhyp (msg x12) (msg (x2 1 0)) H. 
funapptrmhyp (msg (to x12)) (msg (to (x2 1 0))) H. 
funapptrmhyp (bol (eqm (to x12) (V 1))) (bol (eqm (to (x2 1 0)) (V 1))) H.
funapptrmhyp (msg (pi1 (x2 0 1 ))) (msg (pi1 (x2 1 0))) H.
 restrsublis H.

(**********************************************************)
pose proof(blindness 3 8 10 0 1 (b 0 7) (b 1 7) ((Mvar 0), (Mvar 1)) ((Mvar 0), (Mvar 1))  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                                                           msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2) ;msg (sk 3)] ).
simpl in H.
aplyprojn 1 15 H ;try split; try reflexivity.  
pose proof (fresh_commit 
1 7 10 0 7 10 9 [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
       msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2);  msg (sk 3);
       msg (N 3); msg (b 0 7); msg (b 1 7); msg (blind (b 0 7) (pk 3) (r 8))] [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
      msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); msg (sk 3);
      msg (N 3); msg (b 0 7); msg (b 1 7); msg (blind (b 1 7) (pk 3) (r 8))]).  simpl in H0. 
apply H0 in H;try reflexivity.
appconst H.
x1checks H. clear H0.
 funapptrmhyp (msg (sign (sk 1) (e (b 0 7) 8)))  (msg (sign (sk 1) (e (b 1 7) 8))) H.
 funapptrmhyp (msg ((e (b 0 7) 8), (sign (sk 1) (e (b 0 7) 8))))  (msg ((e (b 1 7) 8), (sign (sk 1) (e (b 1 7) 8)))) H.
 funapptrmhyp (msg ((pk 1), ((e (b 0 7) 8), (sign (sk 1) (e (b 0 7) 8)))))  (msg ((pk 1), ((e (b 1 7) 8), (sign (sk 1) (e (b 1 7) 8))))) H.
  funapptrmhyp (msg (sign (sk 2) (e (b 1 9) 10)))  (msg (sign (sk 2) (e (b 0 9) 10))) H. 
 funapptrmhyp  (msg ((e (b 1 9) 10), (sign (sk 2) (e (b 1 9) 10))))  (msg ((e (b 0 9) 10), (sign (sk 2) (e (b 0 9) 10)))) H.
 funapptrmhyp  (msg (pk 2, ((e (b 1 9) 10), (sign (sk 2) (e (b 1 9) 10)))))  (msg (pk 2, ((e (b 0 9) 10), (sign (sk 2) (e (b 0 9) 10))))) H.

adminchecks x11 x11 H.
funapptrmhyp (msg (ifm  (eqm (to x11) (V 2))  ((pk 2), ( (e (b 1 9) 10),  (sign (sk 2) (e (b 1 9) 10))))
                                                 (admin x11)   )) (msg (ifm  (eqm (to x11) (V 2))  ((pk 2), ( (e (b 0 9) 10),  (sign (sk 2) (e (b 0 9) 10))))
                                                  (admin x11)   )) H.
funapptrmhyp (msg (q0 )) (msg (q0 1 0)) H.
funapptrmhyp (msg x12) (msg (x2 1 0)) H. 
funapptrmhyp (msg (to x12)) (msg (to (x2 1 0))) H. 
funapptrmhyp (bol (eqm (to x12) (V 1))) (bol (eqm (to (x2 1 0)) (V 1))) H.
funapptrmhyp (msg (pi1 (x2 0 1 ))) (msg (pi1 (x2 1 0))) H.
restrsublis H.
(**********************************************************************)

simpl.
apply IFBRANCH_M2 with (ml1:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); bol (eqm (to x11) (V 1))]) (ml2:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); bol (eqm (to x11) (V 1))]) .
simpl. 
apply IFBRANCH_M1 with (ml1:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); bol (eqm (to x11) (V 1)); 
    bol (eqm (to x11) (V 2));
    msg (pk 2, (e (b 1 9) 10, sign (sk 2) (e (b 1 9) 10)))]) (ml2:=  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); bol (eqm (to x11) (V 1)); 
   bol (eqm (to x11) (V 2));
   msg (pk 2, (e (b 0 9) 10, sign (sk 2) (e (b 0 9) 10)))]) . simpl.

pose proof(blindness 3 8 10 0 1 (b 0 7) (b 1 7) ((Mvar 0), (Mvar 1)) ((Mvar 0), (Mvar 1))  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                                                           msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2) ;msg (sk 3)] ).
simpl in H. 
aplyprojn 1 15 H ;try split; try reflexivity.  
pose proof (fresh_commit 
1 7 10 0 7 10 9 [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
       msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2);  msg (sk 3);
       msg (N 3); msg (b 0 7); msg (b 1 7); msg (blind (b 0 7) (pk 3) (r 8))] [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
      msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); msg (sk 3);
      msg (N 3); msg (b 0 7); msg (b 1 7); msg (blind (b 1 7) (pk 3) (r 8))]).  simpl in H0. 
apply H0 in H;try reflexivity. clear H0.
appconst H.
x1checks H.
 funapptrmhyp (msg (sign (sk 1) (e (b 0 7) 8)))  (msg (sign (sk 1) (e (b 1 7) 8))) H.
 funapptrmhyp (msg ((e (b 0 7) 8), (sign (sk 1) (e (b 0 7) 8))))  (msg ((e (b 1 7) 8), (sign (sk 1) (e (b 1 7) 8)))) H.
 funapptrmhyp (msg ((pk 1), ((e (b 0 7) 8), (sign (sk 1) (e (b 0 7) 8)))))  (msg ((pk 1), ((e (b 1 7) 8), (sign (sk 1) (e (b 1 7) 8))))) H.
 funapptrmhyp (msg (sign (sk 2) (e (b 1 9) 10)))  (msg (sign (sk 2) (e (b 0 9) 10))) H.
 funapptrmhyp (msg ((e (b 1 9) 10), (sign (sk 2) (e (b 1 9) 10))))  (msg ((e (b 0 9) 10), (sign (sk 2) (e (b 0 9) 10)))) H.
 funapptrmhyp (msg ((pk 2), ((e (b 1 9) 10), (sign (sk 2) (e (b 1 9) 10)))))  (msg ((pk 2), ((e (b 0 9) 10), (sign (sk 2) (e (b 0 9) 10))))) H.
  funapptrmhyp (msg (sign (sk 2) (e (b 1 9) 10)))  (msg (sign (sk 2) (e (b 0 9) 10))) H. 
 funapptrmhyp  (msg ((e (b 1 9) 10), (sign (sk 2) (e (b 1 9) 10))))  (msg ((e (b 0 9) 10), (sign (sk 2) (e (b 0 9) 10)))) H.
 funapptrmhyp  (msg (pk 2, ((e (b 1 9) 10), (sign (sk 2) (e (b 1 9) 10)))))  (msg (pk 2, ((e (b 0 9) 10), (sign (sk 2) (e (b 0 9) 10))))) H.

adminchecks x11 x11 H.
funapptrmhyp (msg (ifm  (eqm (to x11) (V 2))  ((pk 2), ( (e (b 1 9) 10),  (sign (sk 2) (e (b 1 9) 10))))
                                                 (admin x11)   )) (msg (ifm  (eqm (to x11) (V 2))  ((pk 2), ( (e (b 0 9) 10),  (sign (sk 2) (e (b 0 9) 10))))
                                                  (admin x11)   )) H.
funapptrmhyp (msg (q0 )) (msg (q0 1 0)) H.
funapptrmhyp (msg x12) (msg (x2 1 0)) H. 
funapptrmhyp (msg (to x12)) (msg (to (x2 1 0))) H. 
funapptrmhyp (bol (eqm (to x12) (V 2))) (bol (eqm (to (x2 1 0)) (V 2))) H.
funapptrmhyp (msg (pi1 (x2 0 1 ))) (msg (pi1 (x2 1 0))) H.
restrsublis H.
(***************************************************************************)
simpl.

apply IFBRANCH_M1 with (ml1:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); bol (eqm (to x11) (V 1)); 
    bol (eqm (to x11) (V 2));
    msg (pk 2, (e (b 1 9) 10, sign (sk 2) (e (b 1 9) 10)));
    bol
      (eqm (to x12) (V 2)) & (bacc (pk 3) (b 1 9) (r 10) (pi2 x12))]) (ml2:=  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); bol (eqm (to x11) (V 1)); 
   bol (eqm (to x11) (V 2));
   msg (pk 2, (e (b 0 9) 10, sign (sk 2) (e (b 0 9) 10)));
   bol
     (eqm (to (x2 1 0)) (V 2)) & (bacc (pk 3) (b 0 9) (r 10) (pi2 (x2 1 0)))]).
simpl.


pose proof(blindness 3 8 10 0 1 (b 0 7) (b 1 7) ((Mvar 0), (Mvar 1)) ((Mvar 0), (Mvar 1))  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                                                           msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2) ;msg (sk 3)] ).
simpl in H.
aplyprojn 1 15 H ;try split; try reflexivity.  
pose proof (fresh_commit 
1 7 10 0 7 10 9 [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
       msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2);  msg (sk 3);
       msg (N 3); msg (b 0 7); msg (b 1 7); msg (blind (b 0 7) (pk 3) (r 8))] [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
      msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); msg (sk 3);
      msg (N 3); msg (b 0 7); msg (b 1 7); msg (blind (b 1 7) (pk 3) (r 8))]).  simpl in H0. 
apply H0 in H;try reflexivity. clear H0.
appconst H.
x1checks H.
 funapptrmhyp (msg (sign (sk 1) (e (b 0 7) 8)))  (msg (sign (sk 1) (e (b 1 7) 8))) H.
 funapptrmhyp (msg ((e (b 0 7) 8), (sign (sk 1) (e (b 0 7) 8))))  (msg ((e (b 1 7) 8), (sign (sk 1) (e (b 1 7) 8)))) H.
 funapptrmhyp (msg ((pk 1), ((e (b 0 7) 8), (sign (sk 1) (e (b 0 7) 8)))))  (msg ((pk 1), ((e (b 1 7) 8), (sign (sk 1) (e (b 1 7) 8))))) H.
  funapptrmhyp (msg (sign (sk 2) (e (b 1 9) 10)))  (msg (sign (sk 2) (e (b 0 9) 10))) H. 
 funapptrmhyp  (msg ((e (b 1 9) 10), (sign (sk 2) (e (b 1 9) 10))))  (msg ((e (b 0 9) 10), (sign (sk 2) (e (b 0 9) 10)))) H.
 funapptrmhyp  (msg (pk 2, ((e (b 1 9) 10), (sign (sk 2) (e (b 1 9) 10)))))  (msg (pk 2, ((e (b 0 9) 10), (sign (sk 2) (e (b 0 9) 10))))) H.

adminchecks x11 x11 H.
funapptrmhyp (msg (ifm  (eqm (to x11) (V 2))  ((pk 2), ( (e (b 1 9) 10),  (sign (sk 2) (e (b 1 9) 10))))
                                                 (admin x11)   )) (msg (ifm  (eqm (to x11) (V 2))  ((pk 2), ( (e (b 0 9) 10),  (sign (sk 2) (e (b 0 9) 10))))
                                                  (admin x11)   )) H.
funapptrmhyp (msg (q0 )) (msg (q0 1 0)) H.
funapptrmhyp (msg x12) (msg (x2 1 0)) H. 
funapptrmhyp (msg (to x12)) (msg (to (x2 1 0))) H. 
funapptrmhyp (bol (eqm (to x12) (V 1))) (bol (eqm (to (x2 1 0)) (V 1))) H.

reswap_in 13 49 H. 
apply fresh_commit with (l1:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
       msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); 
       msg (sk 3); msg (N 3); msg (b 0 7); msg (b 1 7);
       bol (eqm (to x12) (V 1)); msg (e (b 1 9) 10); 
       msg ok; msg (V 1); msg (V 2); msg O; msg x11; 
       msg (to x11); bol (eqm (to x11) (V 1)); bol (eqm (to x11) (V 2));
       bol (eqm (to x11) (pk 3)); msg (sign (sk 1) (e (b 0 7) 8));
       msg (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8));
       msg (pk 1, (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8)));
       msg (sign (sk 2) (e (b 1 9) 10));
       msg (e (b 1 9) 10, sign (sk 2) (e (b 1 9) 10));
       msg (pk 2, (e (b 1 9) 10, sign (sk 2) (e (b 1 9) 10))); 
       msg (pi1 x11); msg (pi1 (pi1 x11)); msg (pi2 (pi1 x11));
       msg (pi1 (pi2 (pi1 x11))); msg (pi2 (pi2 (pi1 x11))); 
       msg (pi2 x11); msg (pi1 (pi2 x11)); msg (pi2 (pi2 x11));
       msg (pi1 (pi2 (pi2 x11))); msg (pi2 (pi2 (pi2 x11)));
       msg (bsign (sk 3) (pi1 (pi2 (pi1 x11))));
       msg (bsign (sk 3) (pi1 (pi2 (pi2 x11))));
       msg
         (bsign (sk 3) (pi1 (pi2 (pi1 x11))),
         bsign (sk 3) (pi1 (pi2 (pi2 x11))));
       bol (ver (pi1 (pi1 x11)) (pi1 (pi2 (pi1 x11))) (pi2 (pi2 (pi1 x11))));
       bol (ver (pi1 (pi2 x11)) (pi1 (pi2 (pi2 x11))) (pi2 (pi2 (pi2 x11))));
       msg
         (ifm (eqm (to x11) (V 2))
            (pk 2, (e (b 1 9) 10, sign (sk 2) (e (b 1 9) 10))) 
            (admin x11)); msg (q0 ); msg x12; 
       msg (to x12)]) (l2:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
      msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); 
      msg (sk 3); msg (N 3); msg (b 0 7); msg (b 1 7);
      bol (eqm (to (x2 1 0)) (V 1)); msg (e (b 0 9) 10); 
      msg ok; msg (V 1); msg (V 2); msg O; msg x11; 
      msg (to x11); bol (eqm (to x11) (V 1)); bol (eqm (to x11) (V 2));
      bol (eqm (to x11) (pk 3)); msg (sign (sk 1) (e (b 1 7) 8));
      msg (e (b 1 7) 8, sign (sk 1) (e (b 1 7) 8));
      msg (pk 1, (e (b 1 7) 8, sign (sk 1) (e (b 1 7) 8)));
      msg (sign (sk 2) (e (b 0 9) 10));
      msg (e (b 0 9) 10, sign (sk 2) (e (b 0 9) 10));
      msg (pk 2, (e (b 0 9) 10, sign (sk 2) (e (b 0 9) 10))); 
      msg (pi1 x11); msg (pi1 (pi1 x11)); msg (pi2 (pi1 x11));
      msg (pi1 (pi2 (pi1 x11))); msg (pi2 (pi2 (pi1 x11))); 
      msg (pi2 x11); msg (pi1 (pi2 x11)); msg (pi2 (pi2 x11));
      msg (pi1 (pi2 (pi2 x11))); msg (pi2 (pi2 (pi2 x11)));
      msg (bsign (sk 3) (pi1 (pi2 (pi1 x11))));
      msg (bsign (sk 3) (pi1 (pi2 (pi2 x11))));
      msg
        (bsign (sk 3) (pi1 (pi2 (pi1 x11))),
        bsign (sk 3) (pi1 (pi2 (pi2 x11))));
      bol (ver (pi1 (pi1 x11)) (pi1 (pi2 (pi1 x11))) (pi2 (pi2 (pi1 x11))));
      bol (ver (pi1 (pi2 x11)) (pi1 (pi2 (pi2 x11))) (pi2 (pi2 (pi2 x11))));
      msg
        (ifm (eqm (to x11) (V 2))
           (pk 2, (e (b 0 9) 10, sign (sk 2) (e (b 0 9) 10))) 
           (admin x11)); msg (q0 1 0); msg (x2 1 0); 
      msg (to (x2 1 0))]) (0:= 0) (1:=7) (n3:= 8) (n4:= 1) (n5:= 7) (n6:=8) (n7:=13) in H; simpl in H; try reflexivity.
apply fresh_blind with (l1:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
       msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); 
       msg (sk 3); msg (N 3); msg (b 0 7); msg (b 1 7);
       bol (eqm (to x12) (V 1)); msg (e (b 1 9) 10); 
       msg ok; msg (V 1); msg (V 2); msg O; msg x11; 
       msg (to x11); bol (eqm (to x11) (V 1)); bol (eqm (to x11) (V 2));
       bol (eqm (to x11) (pk 3)); msg (sign (sk 1) (e (b 0 7) 8));
       msg (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8));
       msg (pk 1, (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8)));
       msg (sign (sk 2) (e (b 1 9) 10));
       msg (e (b 1 9) 10, sign (sk 2) (e (b 1 9) 10));
       msg (pk 2, (e (b 1 9) 10, sign (sk 2) (e (b 1 9) 10))); 
       msg (pi1 x11); msg (pi1 (pi1 x11)); msg (pi2 (pi1 x11));
       msg (pi1 (pi2 (pi1 x11))); msg (pi2 (pi2 (pi1 x11))); 
       msg (pi2 x11); msg (pi1 (pi2 x11)); msg (pi2 (pi2 x11));
       msg (pi1 (pi2 (pi2 x11))); msg (pi2 (pi2 (pi2 x11)));
       msg (bsign (sk 3) (pi1 (pi2 (pi1 x11))));
       msg (bsign (sk 3) (pi1 (pi2 (pi2 x11))));
       msg
         (bsign (sk 3) (pi1 (pi2 (pi1 x11))),
         bsign (sk 3) (pi1 (pi2 (pi2 x11))));
       bol (ver (pi1 (pi1 x11)) (pi1 (pi2 (pi1 x11))) (pi2 (pi2 (pi1 x11))));
       bol (ver (pi1 (pi2 x11)) (pi1 (pi2 (pi2 x11))) (pi2 (pi2 (pi2 x11))));
       msg
         (ifm (eqm (to x11) (V 2))
            (pk 2, (e (b 1 9) 10, sign (sk 2) (e (b 1 9) 10))) 
            (admin x11)); msg (q0 ); msg x12; 
       msg (to x12)]) (l2:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
      msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); 
      msg (sk 3); msg (N 3); msg (b 0 7); msg (b 1 7);
      bol (eqm (to (x2 1 0)) (V 1)); msg (e (b 0 9) 10); 
      msg ok; msg (V 1); msg (V 2); msg O; msg x11; 
      msg (to x11); bol (eqm (to x11) (V 1)); bol (eqm (to x11) (V 2));
      bol (eqm (to x11) (pk 3)); msg (sign (sk 1) (e (b 1 7) 8));
      msg (e (b 1 7) 8, sign (sk 1) (e (b 1 7) 8));
      msg (pk 1, (e (b 1 7) 8, sign (sk 1) (e (b 1 7) 8)));
      msg (sign (sk 2) (e (b 0 9) 10));
      msg (e (b 0 9) 10, sign (sk 2) (e (b 0 9) 10));
      msg (pk 2, (e (b 0 9) 10, sign (sk 2) (e (b 0 9) 10))); 
      msg (pi1 x11); msg (pi1 (pi1 x11)); msg (pi2 (pi1 x11));
      msg (pi1 (pi2 (pi1 x11))); msg (pi2 (pi2 (pi1 x11))); 
      msg (pi2 x11); msg (pi1 (pi2 x11)); msg (pi2 (pi2 x11));
      msg (pi1 (pi2 (pi2 x11))); msg (pi2 (pi2 (pi2 x11)));
      msg (bsign (sk 3) (pi1 (pi2 (pi1 x11))));
      msg (bsign (sk 3) (pi1 (pi2 (pi2 x11))));
      msg
        (bsign (sk 3) (pi1 (pi2 (pi1 x11))),
        bsign (sk 3) (pi1 (pi2 (pi2 x11))));
      bol (ver (pi1 (pi1 x11)) (pi1 (pi2 (pi1 x11))) (pi2 (pi2 (pi1 x11))));
      bol (ver (pi1 (pi2 x11)) (pi1 (pi2 (pi2 x11))) (pi2 (pi2 (pi2 x11))));
      msg
        (ifm (eqm (to x11) (V 2))
           (pk 2, (e (b 0 9) 10, sign (sk 2) (e (b 0 9) 10))) 
           (admin x11)); msg (q0 1 0); msg (x2 1 0); 
      msg (to (x2 1 0))]) (0:= 0) (1:=13) (n3:= 8) (n4:= 1) (n5:= 13) (n6:=8) (n7:=14) in H; simpl in H; try reflexivity.
restrsublis H.
simpl.
(********************************************************************)
simpl. 

pose proof(blindness 3 8 10 0 1 (b 0 7) (b 1 7) ((Mvar 0), (Mvar 1)) ((Mvar 0), (Mvar 1))  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                                                           msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2) ;msg (sk 3)] ).
simpl in H.
aplyprojn 1 15 H ;try split; try reflexivity.  
pose proof (fresh_commit 
1 7 10 0 7 10 9 [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
       msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2);  msg (sk 3);
       msg (N 3); msg (b 0 7); msg (b 1 7); msg (blind (b 0 7) (pk 3) (r 8))] [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
      msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); msg (sk 3);
      msg (N 3); msg (b 0 7); msg (b 1 7); msg (blind (b 1 7) (pk 3) (r 8))]).  simpl in H0. 
apply H0 in H;try reflexivity.
appconst H.
x1checks H. clear H0.
 funapptrmhyp (msg (sign (sk 1) (e (b 0 7) 8)))  (msg (sign (sk 1) (e (b 1 7) 8))) H.
 funapptrmhyp (msg ((e (b 0 7) 8), (sign (sk 1) (e (b 0 7) 8))))  (msg ((e (b 1 7) 8), (sign (sk 1) (e (b 1 7) 8)))) H.
 funapptrmhyp (msg ((pk 1), ((e (b 0 7) 8), (sign (sk 1) (e (b 0 7) 8)))))  (msg ((pk 1), ((e (b 1 7) 8), (sign (sk 1) (e (b 1 7) 8))))) H.
  funapptrmhyp (msg (sign (sk 2) (e (b 1 9) 10)))  (msg (sign (sk 2) (e (b 0 9) 10))) H. 
 funapptrmhyp  (msg ((e (b 1 9) 10), (sign (sk 2) (e (b 1 9) 10))))  (msg ((e (b 0 9) 10), (sign (sk 2) (e (b 0 9) 10)))) H.
 funapptrmhyp  (msg (pk 2, ((e (b 1 9) 10), (sign (sk 2) (e (b 1 9) 10)))))  (msg (pk 2, ((e (b 0 9) 10), (sign (sk 2) (e (b 0 9) 10))))) H.

adminchecks x11 x11 H.
funapptrmhyp (msg (ifm  (eqm (to x11) (V 2))  ((pk 2), ( (e (b 1 9) 10),  (sign (sk 2) (e (b 1 9) 10))))
                                                 (admin x11)   )) (msg (ifm  (eqm (to x11) (V 2))  ((pk 2), ( (e (b 0 9) 10),  (sign (sk 2) (e (b 0 9) 10))))
                                                  (admin x11)   )) H.
funapptrmhyp (msg (q0 )) (msg (q0 1 0)) H.
funapptrmhyp (msg x12) (msg (x2 1 0)) H. 
funapptrmhyp (msg (to x12)) (msg (to (x2 1 0))) H. 
funapptrmhyp (bol (eqm (to x12) (V 1))) (bol (eqm (to (x2 1 0)) (V 1))) H.
funapptrmhyp (msg (pi1 (x2 0 1 ))) (msg (pi1 (x2 1 0))) H.
restrsublis H.
restrsublis H. reflexivity.

End foo_prot12.

Ltac ifbranch1 :=
  match goal with
    | [|- (?L1 ++ [msg (ifm ?B1 ?X1 ?Y1)]) ~  (?L2 ++ [msg (ifm ?B2 ?X2 ?Y2)])] => apply IFBRANCH_M1 with (ml1 := L1) (ml2 := L2)
  end.

Ltac ifbranch2 :=
  match goal with
    | [  |- (?L1 ++ [msg (ifm _ _ _)] ++ [msg (ifm _ _ _)]) ~  (?L2 ++ [msg (ifm _ _ _)] ++ [msg (ifm _ _ _)])] => apply IFBRANCH_M2 with (ml1 := L1) (ml2:= L2)
  end.
ifbranch2.
