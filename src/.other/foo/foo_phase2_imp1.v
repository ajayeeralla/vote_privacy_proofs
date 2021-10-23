Load "imp1_phase1".
   
    
(** * FOO Voting Prtocol *)
(** ** Phase-II *)
(** 
<<
- [V1 -> M : { (commit(v0, r), unblind(pkat, c, r'', pi1(x3))) }_pk5 ]

- [V2 -> M : { (commit(v1, r'), unblind(pkat, c, r''', pi2(x3))) }_pk5 ]
>> *)

(** - We assume that Administrator and collector are dishonest
    - Hence, random numbers used to generate keys (pair) of them included in attacker's knowledge *)

(** * ProtocolPhase-I: There are two voters [V1] and [V2], and their corresponding votes [va] and [vb] respectively. *)
 
(** * Frame [phi0]: initial knowledge *)
(** 1-Voter1, 2-Voter2, 3-Administrator, 4-Collector, 5-Mixnet 
[(pk 0)] represents a public key used in commitment shceme. *)

(** Even though different symbols used to distinuish the key generations, for convenience, we use same symbols here in Coq *)

 
(** * Frame [phi3] *) 

Definition x3tt n1 n2 :=  f (conv_mylist_listm (phi0 ++ [bol (eqm (to x1) (V 1));msg (pk 1, (e (b n1 7) 8, sign (sk 1) (e (b n1 7) 8) (r 30)))] ++  [bol (eqm (to (x2t n1)) (V 2)); msg (pk 2, (e (b n2 11) 12, sign (sk 2) (e (b n2 11) 12) (r 32)))])).

Definition x3tf n1 := f (conv_mylist_listm (phi0 ++ [bol (eqm (to x1) (V 1)); msg (pk 1, (e (b n1 7) 8, sign (sk 1) (e (b n1 7) 8) (r 30)))] ++  [bol (eqm (to (x2t n1)) (V 2)); msg O])).

Definition x3ftt n1 n2 := f (conv_mylist_listm (phi0 ++ [bol (eqm (to x1) (V 1)); bol (eqm (to x1) (V 2)); msg (pk 2, (e (b n2 9) 10, sign (sk 2) (e (b n2 9) 10) (r 31)))] ++ [bol (eqm (to (x2ft n2)) (V 1)); msg (pk 1, (e (b n1 13) 14, sign (sk 1) (e (b n1 13) 14) (r 33)))])).
Definition x3ftf n2 := f (conv_mylist_listm (phi0 ++ [bol (eqm (to x1) (V 1)); bol (eqm (to x1) (V 2)); msg (pk 2, (e (b n2 9) 10, sign (sk 2) (e (b n2 9) 10) (r 31)))] ++  [bol (eqm (to (x2ft n2)) (V 1)); msg O])).
Definition x3fff  := f (conv_mylist_listm (phi0 ++ [bol (eqm (to x1) (V 1))] ++ [bol (eqm (to x1) (V 2)); msg O; msg O])). 

(** * Step 1 of Voting phase *)
 
Definition q11 n1 n2 := (ifm (eqm (to (x3tt n1 n2)) (V 1)) & (bacc pkat (b n1 7) (r 8) (pi1 (x3tt n1 n2))) (enc ((b n1 7), (unblind pkat (b n1 7) (r 8) (pi1 (x3tt n1 n2)))) (pk 5) (r 50)) (ifm (eqm (to (x3tt n1 n2)) (V 2)) & (bacc pkat (b n2 11) (r 12) (pi2 (x3tt n1 n2))) (enc ((b n2 11), (unblind pkat (b n2 11) (r 12) (pi2 (x3tt n1 n2)))) (pk 5) (r 51)) O)).

Definition q21 n1 n2 := (ifm (eqm (to (x3ftt n1 n2)) (V 2)) & (bacc pkat (b n2 9) (r 10) (pi2 (x3ftt n1 n2))) (enc ((b n2 9), (unblind pkat (b n2 9) (r 10) (pi2 (x3ftt n1 n2)))) (pk 5) (r 52)) (ifm (eqm (to (x3ftt n1 n2)) (V 1)) & (bacc pkat (b n1 13) (r 14) (pi1 (x3ftt n1 n2))) (enc ((b n1 13), (unblind pkat (b n1 13) (r 14) (pi1 (x3ftt n1 n2)))) (pk 5) (r 54)) O)).

(*****************************************************)

Definition q1_s n1 n2 := (* (ifm (eqm (to (x2t n1)) (V 1))& (bacc pkat (b n1 7) (r 8) (pi1 (x2t n1)))  ok *)
			            (ifm (eqm (to (x2t n1)) (V 2)) (q11 n1 n2) O).
                                                  
Definition q2_s n1 n2 :=  (* (ifm (eqm (to (x2ft n2)) (V 2))& (bacc pkat (b n2 9) (r 10) (pi2 (x2ft n2)))  ok *)
			           (ifm (eqm (to (x2ft n2)) (V 1)) (q21 n1 n2)  O).
                                                 
 
Definition t2 n1 n2 :=  (ifm (eqm (to x1) (V 1)) (q1_s n1 n2)
		    	     (ifm (eqm (to x1) (V 2))  (q2_s n1 n2) O)).

Definition phi3 n1 n2 := (phi2 n1 n2) ++ [msg (t2 n1 n2)].
 Theorem frame3ind: (phi3 0 1) ~ (phi3 1 0).
Proof. unfold phi3, phi2, phi1, phi0, q0, t1, t2, q1, q2, q1_s, q2_s, q11, q21.
simpl.
apply IFBRANCH_M3 with (ml1:= phi0) (ml2:= phi0).
simpl.
apply IFBRANCH_M2 with (ml1:= phi0 ++ [ bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8) (r 30)))])(ml2:= phi0 ++ [bol (eqm (to x1) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (e (b 1 7) 8) (r 30)))]).
simpl.
apply IFBRANCH_M1 with (ml1:= (phi0 ++[ bol (eqm (to x1) (V 1)); msg (pk 1, (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8) (r 30))); bol (eqm (to (x2t 0)) (V 2)); msg (pk 2, (e (b 1 11) 12, sign (sk 2) (e (b 1 11) 12) (r 32)))]))(ml2:= (phi0 ++ [ bol (eqm (to x1) (V 1)); msg (pk 1, (e (b 1 7) 8, sign (sk 1) (e (b 1 7) 8) (r 30))); bol (eqm (to (x2t 1)) (V 2)); msg (pk 2, (e (b 0 11) 12, sign (sk 2) (e (b 0 11) 12) (r 32)))])). 
simpl.
(** TRACE-1 *)
 pose proof( commit_swap (vt 0) (vt 1) _ 7 7 11 11 [ msg (sk 1); msg (sk 2); msg (r 8); msg (r 12); msg (r 30); msg (r 32); msg (r 50); msg (pk 1); msg (pk 2); msg (pk 5); msg pkat; msg (vt 0); msg (vt 1); bol (eqm (to x1) (V 1))]); simpl in H;
assert( (L (vt 0)) # (L (vt 1)));
try eapply len_f1; try eapply len_nonce;
eapply EQmsg' in H0; 
apply H in H0; clear H; rename H0 into H; auto;
appconst H;
x1checks x1 x1 H; simpl;
bterm 0 1 7 H.
(** Appending triple term of voter1 on both sides *)  
funapptrmhyp (msg (sign (sk 1) (e (b 0 7) 8) (r 30))) (msg (sign (sk 1) (e (b 1 7) 8) (r 30))) H;
funapptrmhyp (msg ((e (b 0 7) 8), (sign (sk 1) (e (b 0 7) 8) (r 30)))) (msg ((e (b 1 7) 8),  (sign (sk 1) (e (b 1 7) 8) (r 30)))) H;
funapptrmhyp (msg (pk 1, (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8) (r 30)))) (msg (pk 1, (e (b 1 7) 8, sign (sk 1) (e (b 1 7) 8) (r 30)))) H;
x1checks (x2t 0) (x2t 1) H.
(** Appending second blind term *)
bterm 1 0 11 H;
(** Appending triple term of voter2 on both sides *)  
funapptrmhyp (msg (sign (sk 2) (e (b 1 11) 12) (r 32))) (msg (sign (sk 2) (e (b 0 11) 12) (r 32))) H;
funapptrmhyp (msg ((e (b 1 11) 12), (sign (sk 2) (e (b 1 11) 12) (r 32)))) (msg ((e (b 0 11) 12),  (sign (sk 2) (e (b 0 11) 12) (r 32)))) H;
funapptrmhyp (msg (pk 2, (e (b 1 11) 12, sign (sk 2) (e (b 1 11) 12) (r 32)))) (msg (pk 2, (e (b 0 11) 12, sign (sk 2) (e (b 0 11) 12) (r 32)))) H.
x1checks (x3tt 0 1) (x3tt 1 0) H.
(** append bacc term on both sides *)
bacctac 0 1 7 8 (x3tt 0 1) (x3tt 1 0) H.
funapptrmhyp (bol (eqm (to (x3tt 0 1)) (V 1)) &
      (bacc pkat (b 0 7) (r 8) (pi1 (x3tt 0 1))))  (bol (eqm (to (x3tt 1 0)) (V 1)) & (bacc pkat (b 1 7) (r 8) (pi1 (x3tt 1 0)))) H.
(** append enc term on both sides *) 
funapptrmhyp (msg (unblind pkat (b 0 7) (r 8) (pi1 (x3tt 0 1)))) (msg (unblind pkat (b 1 7) (r 8) (pi1 (x3tt 1 0)))) H. 
funapptrmhyp (msg ((b 0 7), (unblind pkat (b 0 7) (r 8) (pi1 (x3tt 0 1))))) (msg ((b 1 7), (unblind pkat (b 1 7) (r 8) (pi1 (x3tt 1 0))))) H.
funapptrmhyp (msg (enc (b 0 7, unblind pkat (b 0 7) (r 8) (pi1 (x3tt 0 1))) (pk 5) (r 50))) (msg (enc (b 1 7, unblind pkat (b 1 7) (r 8) (pi1 (x3tt 1 0))) (pk 5) (r 50))) H.
restrsublis H.

(** TRACE-2 *)
simpl. Admitted.

(** Frame [phi 4] *)
 
Definition x4ttt n1 n2 := f (conv_mylist_listm (phi0 ++ [ bol (eqm (to x1) (V 1)); msg (pk 1, (e (b n1 7) 8, sign (sk 1) (e (b n1 7) 8) (r 30))); bol (eqm (to (x2t n1)) (V 2)); msg (pk 2, (e (b n2 11) 12, sign (sk 2) (e (b n2 11) 12) (r 32))); bol (eqm (to (x3tt n1 n2)) (V 1)) & (bacc pkat (b n1 7) (r 8) (pi1 (x3tt n1 n2))); msg (enc (b n1 7, unblind pkat (b n1 7) (r 8) (pi1 (x3tt n1 1))) (pk 5) (r 34))])).

Definition x4tftt n1 n2 := f (conv_mylist_listm (phi0 ++  [bol (eqm (to x1) (V 1)); msg (pk 1, (e (b n1 7) 8, sign (sk 1) (e (b n1 7) 8) (r 30))); bol (eqm (to (x2t n1)) (V 2)); msg (pk 2, (e (b n2 11) 12, sign (sk 2) (e (b n2 11) 12) (r 32))); bol (eqm (to (x3tt n1 n2)) (V 1)) & (bacc pkat (b n1 7) (r 8) (pi1 (x3tt n1 n2))); bol (eqm (to (x3tt n1 n2)) (V 2)) & (bacc pkat (b n2 11) (r 12) (pi2 (x3tt n1 n2)));
    msg (enc (b n2 11, unblind pkat (b n2 11) (r 12) (pi2 (x3tt n1 n2))) (pk 5) (r 35))])).

Definition x4ttff n1 n2 := f (conv_mylist_listm (phi0 ++ [bol (eqm (to x1) (V 1)); msg (pk 1, (e (b n1 7) 8, sign (sk 1) (e (b n1 7) 8) (r 30))); bol (eqm (to (x2t n1)) (V 2)); msg (pk 2, (e (b n2 11) 12, sign (sk 2) (e (b n2 11) 12) (r 32))); bol (eqm (to (x3tt n1 n2)) (V 1)) & (bacc pkat (b n1 7) (r 8) (pi1 (x3tt n1 n2))); bol (eqm (to (x3tt n1 n2)) (V 2)) & (bacc pkat (b n2 11) (r 12) (pi2 (x3tt n1 n2))); 
    msg O])) .
Definition x4fttt n1 n2 := f (conv_mylist_listm (phi0 ++ [ bol (eqm (to x1) (V 1));  bol (eqm (to x1) (V 2)); msg (pk 2, (e (b n2 9) 10, sign (sk 2) (e (b n2 9) 10) (r 31))); bol (eqm (to (x2ft n2)) (V 1)); msg (pk 1, (e (b n1 13) 14, sign (sk 1) (e (b n1 13) 14) (r 33)));
    bol (eqm (to (x3ftt n1 n2)) (V 2)) & (bacc pkat (b n2 9) (r 10) (pi2 (x3ftt n1 n2))); msg (enc (b n2 9, unblind pkat (b n2 9) (r 10) (pi2 (x3ftt n1 n2))) (pk 5) (r 36))]) ).

Definition x4fttft n1 n2 := f (conv_mylist_listm (phi0 ++ [bol (eqm (to x1) (V 1)); 
    bol (eqm (to x1) (V 2));
    msg (pk 2, (e (b n2 9) 10, sign (sk 2) (e (b n2 9) 10) (r 31)));
    bol (eqm (to (x2ft n2)) (V 1));
    msg (pk 1, (e (b n1 13) 14, sign (sk 1) (e (b n1 13) 14) (r 33)));
    bol
      (eqm (to (x3ftt n1 n2)) (V 2)) &
      (bacc pkat (b n2 9) (r 10) (pi2 (x3ftt n1 n2)));
    bol
      (eqm (to (x3ftt n1 n2)) (V 1)) &
      (bacc pkat (b n1 13) (r 14) (pi1 (x3ftt n1 n2)));
    msg
      (enc (b n1 13, unblind pkat (b n1 13) (r 14) (pi1 (x3ftt n1 n2))) 
         (pk 5) (r 37))])).

Definition x4fttff n1 n2 := f (conv_mylist_listm (phi0 ++ [bol (eqm (to x1) (V 1)); 
    bol (eqm (to x1) (V 2));
    msg (pk 2, (e (b n2 9) 10, sign (sk 2) (e (b n2 9) 10) (r 31)));
    bol (eqm (to (x2ft 1)) (V 1));
    msg (pk 1, (e (b n1 13) 14, sign (sk 1) (e (b n1 13) 14) (r 33)));
    bol
      (eqm (to (x3ftt n1 n2)) (V 2)) &
      (bacc pkat (b n2 9) (r 10) (pi2 (x3ftt n1 n2)));
    bol
      (eqm (to (x3ftt n1 n2)) (V 1)) &
      (bacc pkat (b n1 13) (r 14) (pi1 (x3ftt n1 n2))); 
    msg O])) .

Definition x4ttft n1 n2 := f (conv_mylist_listm (phi0 ++ [ bol (eqm (to x1) (V 1));
  msg (pk 1, (e (b n1 7) 8, sign (sk 1) (e (b n1 7) 8) (r 30)));
  bol (eqm (to (x2t n1)) (V 2));
  msg (pk 2, (e (b n2 11) 12, sign (sk 2) (e (b n2 11) 12) (r 32)));
  bol
    (eqm (to (x3tt 0 1)) (V 1)) & (bacc pkat (b 0 7) (r 8) (pi1 (x3tt 0 1)));
  bol
    (eqm (to (x3tt 0 1)) (V 2)) &
    (bacc pkat (b n2 11) (r 12) (pi2 (x3tt n1 n2)));
  msg
    (enc (b n2 11, unblind pkat (b n2 11) (r 12) (pi2 (x3tt n1 n2))) 
       (pk 5) (r 35))])).

(** * Step 2 of Voting phase *)
 Definition q111 n1 n2 :=  (ifm (eqm (to (x4ttt n1 n2)) (V 2)) & (bacc pkat (b n2 11) (r 12) (pi2 (x3tt n1 n2))) (enc ((b n2 11), (unblind pkat (b n2 11) (r 12) (pi2 (x4ttt n1 n2)))) (pk 5) (r 55)) O).

 Definition q112 n1 n2 :=    (ifm (eqm (to (x4ttft n1 n2)) (V 1)) & (bacc pkat (b n1 7) (r 8) (pi1 (x4ttft n1 n2))) (enc ((b n1 7), (unblind pkat (b n1 7) (r 8) (pi1 (x4ttft n1 n2)))) (pk 5) (r 56)) O).

 Definition q211 n1 n2 :=  (ifm (eqm (to (x4fttt n1 n2)) (V 1)) & (bacc pkat (b n1 13) (r 14) (pi1 (x4fttt n1 n2))) (enc ((b n1 13), (unblind pkat (b n1 13) (r 14) (pi1 (x4fttt n1 n2)))) (pk 5) (r 57)) O).

 Definition q212 n1 n2 :=  (ifm (eqm (to (x4fttft n1 n2)) (V 2)) & (bacc pkat (b n2 9) (r 10) (pi2 (x4fttft n1 n2))) (enc ((b n2 9), (unblind pkat (b n2 9) (r 10) (pi2 (x4fttft n1 n2)))) (pk 5) (r 58)) O).

 (** * Step 1 of Voting phase *)
 
Definition q11s n1 n2 := (ifm (eqm (to (x3tt n1 n2)) (V 1)) & (bacc pkat (b n1 7) (r 8) (pi1 (x3tt n1 n2))) (q111 n1 n2) (ifm (eqm (to (x3tt n1 n2)) (V 2)) & (bacc pkat (b n2 11) (r 12) (pi2 (x3tt n1 n2))) (q112 n1 n2) O)).

Definition q21s n1 n2 := (ifm (eqm (to (x3ftt n1 n2)) (V 2)) & (bacc pkat (b n2 9) (r 10) (pi2 (x3ftt n1 n2))) (q211 n1 n2) (ifm (eqm (to (x3ftt n1 n2)) (V 1)) & (bacc pkat (b n1 13) (r 14) (pi1 (x3ftt n1 n2))) (q212 n1 n2) O)).
(*****************************************************)
Definition q1s n1 n2 := (* (ifm (eqm (to (x2t n1)) (V 1))& (bacc pkat (b n1 7) (r 8) (pi1 (x2t n1)))  ok *)
			            (ifm (eqm (to (x2t n1)) (V 2)) (q11s n1 n2) O).
                                                  
Definition q2s n1 n2 :=  (* (ifm (eqm (to (x2ft n2)) (V 2))& (bacc pkat (b n2 9) (r 10) (pi2 (x2ft n2)))  ok *)
			           (ifm (eqm (to (x2ft n2)) (V 1)) (q21s n1 n2)  O).
                                                   
 
Definition t3 n1 n2 :=  (ifm (eqm (to x1) (V 1)) (q1s n1 n2)
		    	     (ifm (eqm (to x1) (V 2))  (q2s n1 n2) O)).

Definition phi4 n1 n2 := (phi3 n1 n2) ++ [msg (t3 n1 n2)].