Load "foo_phase2_imp1".


Theorem frame4ind: (phi4 0 1) ~ (phi4 1 0).
Proof. repeat unfold phi4, phi3, phi2, phi1, q0, t1, t2, t3, q1, q2, q1_s, q2_s, q1s, q2s, q11, q21 , q11s, q21s.  simpl. 
     
(** apply IFBRANCH *)
apply IFBRANCH_M4 with (ml1:= phi0) (ml2:= phi0).
simpl.  unfold q111.
 apply IFBRANCH_M3 with (ml1:= (phi0 ++ [bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8) (r 30)))] )) (ml2:= (phi0 ++[bol (eqm (to x1) (V 1)); msg (pk 1, (e (b 1 7) 8, sign (sk 1) (e (b 1 7) 8) (r 30)))])).
simpl. 
apply IFBRANCH_M2 with (ml1:= (phi0 ++ [bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8) (r 30)));  bol (eqm (to (x2t 0)) (V 2));
    msg (pk 2, (e (b 1 11) 12, sign (sk 2) (e (b 1 11) 12) (r 32)))] )) (ml2:= (phi0 ++[bol (eqm (to x1) (V 1)); msg (pk 1, (e (b 1 7) 8, sign (sk 1) (e (b 1 7) 8) (r 30)));  bol (eqm (to (x2t 1)) (V 2)); msg (pk 2, (e (b 0 11) 12, sign (sk 2) (e (b 0 11) 12) (r 32)))])). simpl.  unfold q111.
apply IFBRANCH_M1 with (ml1:= (phi0 ++ [bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8) (r 30)));  bol (eqm (to (x2t 0)) (V 2));
    msg (pk 2, (e (b 1 11) 12, sign (sk 2) (e (b 1 11) 12) (r 32))); bol (eqm (to (x3tt 0 1)) (V 1)) & (bacc pkat (b 0 7) (r 8) (pi1 (x3tt 0 1))); msg (enc (b 0 7, unblind pkat (b 0 7) (r 8) (pi1 (x3tt 0 1))) (pk 5) (r 50))] )) (ml2:= (phi0 ++[bol (eqm (to x1) (V 1)); msg (pk 1, (e (b 1 7) 8, sign (sk 1) (e (b 1 7) 8) (r 30)));  bol (eqm (to (x2t 1)) (V 2)); msg (pk 2, (e (b 0 11) 12, sign (sk 2) (e (b 0 11) 12) (r 32)));  bol (eqm (to (x3tt 1 0)) (V 1)) & (bacc pkat (b 1 7) (r 8) (pi1 (x3tt 1 0))); msg (enc (b 1 7, unblind pkat (b 1 7) (r 8) (pi1 (x3tt 1 0))) (pk 5) (r 50))])).
simpl.
unfold q111, q112, q211, q212.
(** apply ENCCPA *)
(** l ++ [t1] ++ [t2] ~ l ++ [t1] ++ [t2'] *)

pose proof(ENCCPA' (b 1 9, unblind pkat (b 1 9) (r 10) (pi2 (x4ttt 0 1))) (b 0 9, unblind pkat (b 0 9) (r 10) (pi2 (x4ttt 1 0)))  O 0 5 54 54 (phi0 ++ [ bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8) (r 30)));
    bol (eqm (to (x2t 0)) (V 2));
    msg (pk 2, (e (b 1 11) 12, sign (sk 2) (e (b 1 11) 12) (r 32))); bol (eqm (to (x3tt 0 1)) (V 1)) & (bacc pkat (b 0 7) (r 8) (pi1 (x3tt 0 1))); msg (enc (b 0 7, unblind pkat (b 0 7) (r 8) (pi1 (x3tt 0 1))) (pk 5) (r 50)); bol (eqm (to (x4ttt 0 1)) (V 2)) &
      (bacc pkat (b 1 9) (r 10) (pi2 (x3tt 0 1)))])); try reflexivity.
assert ((L (b 1 9, unblind pkat (b 1 9) (r 10) (pi2 (x4ttt 0 1)))) #  (L (b 0 9, unblind pkat (b 0 9) (r 10) (pi2 (x4ttt 1 0))))).
try apply len_trm4; try apply len_trm3; try apply len_trm2; try apply len_trm1; try apply len_nonce.
apply EQmsg' in H0. apply H in H0;try reflexivity. clear H. simpl in H0.
rename H0 into H.      
(** apply ENCCPA *)
 
(** l ++ [t1] ++ [t2'] ~ l ++ [t1'] ++ [t2'] *)

pose proof(ENCCPA' (b 0 7, unblind pkat (b 0 7) (r 8) (pi1 (x3tt 0 1))) (b 1 7, unblind pkat (b 1 7) (r 8) (pi1 (x3tt 1 0))) O 0 5 50 50 (phi0 ++ [bol (eqm (to x1) (V 1));
      msg (pk 1, (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8) (r 30)));
      bol (eqm (to (x2t 0)) (V 2));
      msg (pk 2, (e (b 1 11) 12, sign (sk 2) (e (b 1 11) 12) (r 32)));
      bol
        (eqm (to (x3tt 0 1)) (V 1)) &
        (bacc pkat (b 0 7) (r 8) (pi1 (x3tt 0 1)));
            bol
        (eqm (to (x4ttt 0 1)) (V 2)) &
        (bacc pkat (b 1 9) (r 10) (pi2 (x3tt 0 1)));
      msg
        (enc (b 0 9, unblind pkat (b 0 9) (r 10) (pi2 (x4ttt 1 0))) 
           (pk 5) (rr (N 54)))]));try reflexivity. simpl. 
(**********************************************)
assert ( (L (b 0 7, unblind pkat (b 0 7) (r 8) (pi1 (x3tt 0 1)))) # (L (b 1 7, unblind pkat (b 1 7) (r 8) (pi1 (x3tt 1 0))))).
    try apply len_trm4; try apply len_trm3; try apply len_trm2; try apply len_trm1; try apply len_nonce.     apply EQmsg' in H1. apply H0 in H1; try reflexivity.

clear H0.
simpl in H1.
restr_swap_in 13 14 H1.
restr_swap_in 12 13 H1.

(** Using transitivity: l ++ [t1;t2] ~ l ++ [t1';t2'] *)
assert(tmp1: [msg (pk 1); msg (pk 2); msg (pk 5); msg pkat; 
       msg (vt 0); msg (vt 1); bol (eqm (to x1) (V 1));
       msg (pk 1, (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8) (r 30)));
       bol (eqm (to (x2t 0)) (V 2));
       msg (pk 2, (e (b 1 11) 12, sign (sk 2) (e (b 1 11) 12) (r 32)));
       bol
         (eqm (to (x3tt 0 1)) (V 1)) &
         (bacc pkat (b 0 7) (r 8) (pi1 (x3tt 0 1)));
       msg
         (enc (b 0 7, unblind pkat (b 0 7) (r 8) (pi1 (x3tt 0 1))) 
            (pk 5) (r 50));
       bol
         (eqm (to (x4ttt 0 1)) (V 2)) &
         (bacc pkat (b 1 9) (r 10) (pi2 (x3tt 0 1)));
       msg
         (enc (b 1 9, unblind pkat (b 1 9) (r 10) (pi2 (x4ttt 0 1))) 
            (pk 5) (rr (N 54)))] ~ [msg (pk 1); msg (pk 2); msg (pk 5); msg pkat; 
       msg (vt 0); msg (vt 1); bol (eqm (to x1) (V 1));
       msg (pk 1, (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8) (r 30)));
       bol (eqm (to (x2t 0)) (V 2));
       msg (pk 2, (e (b 1 11) 12, sign (sk 2) (e (b 1 11) 12) (r 32)));
       bol
         (eqm (to (x3tt 0 1)) (V 1)) &
         (bacc pkat (b 0 7) (r 8) (pi1 (x3tt 0 1)));
       msg
         (enc (b 1 7, unblind pkat (b 1 7) (r 8) (pi1 (x3tt 1 0))) 
            (pk 5) (rr (N 50)));
       bol
         (eqm (to (x4ttt 0 1)) (V 2)) &
         (bacc pkat (b 1 9) (r 10) (pi2 (x3tt 0 1)));
       msg
         (enc (b 0 9, unblind pkat (b 0 9) (r 10) (pi2 (x4ttt 1 0))) 
            (pk 5) (rr (N 54)))]);
try apply EQI_trans with (ml2:= [msg (pk 1); msg (pk 2); msg (pk 5); msg pkat; 
      msg (vt 0); msg (vt 1); bol (eqm (to x1) (V 1));
      msg (pk 1, (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8) (r 30)));
      bol (eqm (to (x2t 0)) (V 2));
      msg (pk 2, (e (b 1 11) 12, sign (sk 2) (e (b 1 11) 12) (r 32)));
      bol
        (eqm (to (x3tt 0 1)) (V 1)) &
        (bacc pkat (b 0 7) (r 8) (pi1 (x3tt 0 1)));
      msg
        (enc (b 0 7, unblind pkat (b 0 7) (r 8) (pi1 (x3tt 0 1))) 
           (pk 5) (r 50));
      bol
        (eqm (to (x4ttt 0 1)) (V 2)) &
        (bacc pkat (b 1 9) (r 10) (pi2 (x3tt 0 1)));
      msg
        (enc (b 0 9, unblind pkat (b 0 9) (r 10) (pi2 (x4ttt 1 0))) 
           (pk 5) (rr (N 54)))]); 
try assumption; clear -tmp1.

(** l ++ [t1'; t2'] ~ l' ++ [t1'; t2'] *)


afunapptrmhyp (msg (TWO, (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                             (pk 5) (rr (N 25))))) (msg (TWO, (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25))))) H1. 
funapptrmhyp (msg (sign (sk 1) (TWO, (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                                          (pk 5) (rr (N 25)))))) (msg (sign (sk 1) (TWO, (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25)))))) H1.

funapptrmhyp (msg ((enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
             (pk 5) (rr (N 25))), (sign (sk 1) (TWO, (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
             (pk 5) (rr (N 25))))))) (msg  ((enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25))), (sign (sk 1) (TWO, (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25))))))) H1. 
do 3 dropone_in H1. 
do 3 (restrproj_in 17 H1).  
restr_swap_in 16 17 H1.

(** subgoal 1 *)  
   (pose proof( commit_swap (vt 0) (vt 1) _ 7 7 11 11 [ msg (sk 1); msg (sk 2); msg (r 8); msg (r 12); msg (r 30); msg (r 32); msg (pk 1); msg (pk 2); msg (pk 5); msg pkat; msg (vt 0); msg (vt 1); bol (eqm (to x1) (V 1))]); simpl in H;
assert( (L (vt 0)) # (L (vt 1)));
try eapply len_f1; try eapply len_nonce;
eapply EQmsg' in H0; 
apply H in H0; clear H; rename H0 into H; try reflexivity;
appconst H;
x1checks x1 x1 H; simpl;
bterm 0 1 7 H;
(** Appending triple term of voter1 on both sides *) 
funapptrmhyp (msg (sign (sk 1) (e (b 0 7) 8) (r 30))) (msg (sign (sk 1) (e (b 1 7) 8) (r 30))) H;
funapptrmhyp (msg ((e (b 0 7) 8), (sign (sk 1) (e (b 0 7) 8) (r 30)))) (msg ((e (b 1 7) 8),  (sign (sk 1) (e (b 1 7) 8) (r 30)))) H;
funapptrmhyp (msg (pk 1, (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8) (r 30)))) (msg (pk 1, (e (b 1 7) 8, sign (sk 1) (e (b 1 7) 8) (r 30)))) H;
x1checks (x2t 0) (x2t 1) H;
(** Appending second blind term *)
bterm 1 0 11 H;
(** Appending triple term of voter2 on both sides *)  
funapptrmhyp (msg (sign (sk 2) (e (b 1 11) 12) (r 32))) (msg (sign (sk 2) (e (b 0 11) 12) (r 32))) H;
funapptrmhyp (msg ((e (b 1 11) 12), (sign (sk 2) (e (b 1 11) 12) (r 32)))) (msg ((e (b 0 11) 12),  (sign (sk 2) (e (b 0 11) 12) (r 32)))) H;
funapptrmhyp (msg (pk 2, (e (b 1 11) 12, sign (sk 2) (e (b 1 11) 12) (r 32)))) (msg (pk 2, (e (b 0 11) 12, sign (sk 2) (e (b 0 11) 12) (r 32)))) H;
(** Reduce goal if hypothesis redundantly contain goal *)
restrsublis H; simpl).

(** goal-3 *)
apply IFBRANCH_M2 with (ml1:= (phi0 ++ [bol (eqm (to x1) (V 1))])) (ml2:= (phi0 ++ [bol (eqm (to x1) (V 1))]));simpl.
                                                                                                                 try (apply IFBRANCH_M1 with (ml1:= (phi0 ++ [bol (eqm (to x1) (V 1)); bol (eqm (to x1) (V 2));
    msg (pk 2, (e (b 1 9) 10, sign (sk 2) (e (b 1 9) 10) (r 31)))])) (ml2:= (phi0 ++ [bol (eqm (to x1) (V 1)); bol (eqm (to x1) (V 2));
    msg (pk 2, (e (b 0 9) 10, sign (sk 2) (e (b 0 9) 10) (r 31)))]));  
 pose proof( commit_swap (vt 1) (vt 0) _ 9 9 13 13 [ msg (sk 1); msg (sk 2); msg (r 10); msg (r 14); msg (r 31); msg (r 33); msg (pk 1); msg (pk 2); msg (pk 5); msg pkat; msg (vt 0); msg (vt 1); bol (eqm (to x1) (V 1));  bol (eqm (to x1) (V 2))]); simpl in H;
assert( (L (vt 1)) # (L (vt 0)));
try eapply len_f1;  try eapply len_nonce;
eapply EQmsg' in H0;
apply H in H0; clear H; rename H0 into H; try reflexivity;
appconst H;
bterm 1 0 9 H;
(** Appending triple term of voter1 on both sides *) 
funapptrmhyp (msg (sign (sk 2) (e (b 1 9) 10) (r 31))) (msg (sign (sk 2) (e (b 0 9) 10) (r 31))) H;
funapptrmhyp (msg ((e (b 1 9) 10), (sign (sk 2) (e (b 1 9) 10) (r 31)))) (msg ((e (b 0 9) 10),  (sign (sk 2) (e (b 0 9) 10) (r 31)))) H;
funapptrmhyp (msg (pk 2, (e (b 1 9) 10, sign (sk 2) (e (b 1 9) 10) (r 31)))) (msg (pk 2, (e (b 0 9) 10, sign (sk 2) (e (b 0 9) 10) (r 31)))) H;
x1checks (x2ft 1) (x2ft 0) H;
(** Appending second blind term *)
bterm  0 1 13 H;
(** Appending triple term of voter2 on both sides *)  
funapptrmhyp (msg (sign (sk 1) (e (b 0 13) 14) (r 33))) (msg (sign (sk 1) (e (b 1 13) 14) (r 33))) H;
funapptrmhyp (msg ((e (b 0 13) 14), (sign (sk 1) (e (b 0 13) 14) (r 33)))) (msg ((e (b 1 13) 14),  (sign (sk 1) (e (b 1 13) 14) (r 33)))) H;
funapptrmhyp (msg (pk 1, (e (b 0 13) 14, sign (sk 1) (e (b 0 13) 14) (r 33)))) (msg (pk 1, (e (b 1 13) 14, sign (sk 1) (e (b 1 13) 14) (r 33)))) H;
(** Reduce goal if hypothesis redundantly contain goal *)
restrsublis H; simpl). reflexivity.

(** Using [RESTR] axiom we get frame1 indistinguishability *)
Qed.
Theorem frame3ind: (phi3 0 1) ~ (phi3 1 0).
Proof. unfold phi3, phi2, phi1, phi0, q0, t1, t2, q1, q2, q1_s, q2_s, q11, q21.
simpl.
Theorem frame1ind: (phi1 0 1) ~ (phi1 1 0).
Proof. pose proof(frame2ind). unfold phi2 in H; simpl in H; restrproj_in 8 H; try assumption. Qed.