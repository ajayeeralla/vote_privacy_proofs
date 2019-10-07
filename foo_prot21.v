Load "foo_prot2".
   
Theorem frame4ind: (phi4 0 1) ~ (phi4 1 0).
Proof. repeat unfold phi4, phi3, phi2, phi1. simpl. repeat unfold t1, t2, t3. repeat unfold q1, q1_s, q2_s, q1_ss, q2_ss. repeat unfold q11_s, q21_s, q22_s, q12_s. repeat unfold q11, q21, q121, q122, q221, q222, q111. repeat unfold q12, q22, q211. repeat unfold q0, q1.
     
(** apply IFBRANCH *)
apply IFBRANCH_M4 with (ml1:= phi0) (ml2:= phi0).
simpl.
apply IFBRANCH_M3 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)))] ) (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)))]).
simpl.
apply IFBRANCH_M2 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
    bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
    msg ok]) (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)));
   bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)));
   msg ok]).
simpl.  apply IFBRANCH_M1 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
    bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
    msg ok; bol (eqm (to (x3tt 0)) (V 2));
    msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)))]) (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)));
   bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)));
   msg ok; bol (eqm (to (x3tt 1)) (V 2));
   msg (pk 2, (e (b 0 19) 20, sign (sk 2) (ONE, e (b 0 19) 20)))]).
simpl.  
(** subgoal *) 
pose proof( commit_swap (vt 0) (vt 1) _ 7 7 19 19 [ msg (sk 1); msg (sk 2); msg (r 8); msg (r 20); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1)); bol (eqm (to x1) (V 2))]); simpl in H.
assert( (L (vt 0)) # (L (vt 1))).
eapply len_f1; eapply len_nonce.
eapply EQmsg' in H0. 
apply H in H0; clear H; rename H0 into H; try reflexivity.
appconst H.
x1checks x1 x1 H. simpl.
bterm 0 1 7 H.
funapp_vtrm 1 0 1 7 8 ONE H.
x1checks (x2t 0) (x2t 1) H.
bacctac 0 1 7 8 (x2t 0) (x2t 1) H.
funapptrmhyp (bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)))) 
(bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)))) H.
x1checks (x3tt 0) (x3tt 1) H.
bterm 1 0 19 H.
funapp_vtrm 2 1 0 19 20 ONE H.
x1checks (x4ttt 0 1) (x4ttt 1 0) H.
bacctac 1 0 19 20 (x4ttt 0 1) (x4ttt 1 0) H. 
funapptrmhyp (bol (eqm (to (x4ttt 0 1)) (V 2))&(bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1)))) (bol (eqm (to (x4ttt 1 0)) (V 2))&(bacc (pk 3) (b 0 19) (r 20) (pi2 (x4ttt 1 0)))) H.
restrsublis H. 
(** subgoal *)
pose proof( commit_swap (vt 0) (vt 1) _ 7 7 19 19 [ msg (sk 1); msg (sk 2); msg (r 8); msg (r 20); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1)); bol (eqm (to x1) (V 2))]); simpl in H.
assert( (L (vt 0)) # (L (vt 1))).
eapply len_f1; eapply len_nonce.
eapply EQmsg' in H0. 
apply H in H0; clear H; rename H0 into H; try reflexivity.
appconst H.
x1checks x1 x1 H. simpl.
bterm 0 1 7 H.
funapp_vtrm 1 0 1 7 8 ONE H.
x1checks (x2t 0) (x2t 1) H.
bacctac 0 1 7 8 (x2t 0) (x2t 1) H.
funapptrmhyp (bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)))) 
(bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)))) H.
x1checks (x3tt 0) (x3tt 1) H.
bterm 1 0 19 H.
funapp_vtrm 2 1 0 19 20 ONE H. 
x1checks (x4ttt 0 1) (x4ttt 1 0) H.
bacctac 1 0 19 20 (x4ttt 0 1) (x4ttt 1 0) H.
unfold andb.
funapptrmhyp (bol (ifb (eqm (to (x4ttt 0 1)) (V 2)) (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1))) FAlse)) (bol (ifb (eqm (to (x4ttt 1 0)) (V 2)) (bacc (pk 3) (b 0 19) (r 20) (pi2 (x4ttt 1 0))) FAlse)) H.
restrsublis H.
(** subgoal *)
simpl. 
pose proof( commit_swap (vt 0) (vt 1) _ 7 7 19 19 [ msg (sk 1); msg (sk 2); msg (r 8); msg (r 20); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1)); bol (eqm (to x1) (V 2))]); simpl in H.
assert( (L (vt 0)) # (L (vt 1))).
eapply len_f1; eapply len_nonce.
eapply EQmsg' in H0.
apply H in H0; clear H; rename H0 into H; try reflexivity.
appconst H.
x1checks x1 x1 H. simpl.
bterm 0 1 7 H.
funapp_vtrm 1 0 1 7 8 ONE H.
x1checks (x2t 0) (x2t 1) H.
bacctac 0 1 7 8 (x2t 0) (x2t 1) H.
funapptrmhyp (bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)))) 
(bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)))) H.
x1checks (x3tt 0) (x3tt 1) H.
restrsublis H. 
(** subgoal *) 
simpl. 
apply IFBRANCH_M3 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
    bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)))]) (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)));
   bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)))]).
simpl. simpl. 
apply IFBRANCH_M2 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
    bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
    bol (eqm (to (x2t 0)) (V 2));
    msg (pk 2, (e (b 1 11) 12, sign (sk 2) (ONE, e (b 1 11) 12)))]) (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)));
   bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)));
   bol (eqm (to (x2t 1)) (V 2));
   msg (pk 2, (e (b 0 11) 12, sign (sk 2) (ONE, e (b 0 11) 12)))]).
simpl.
apply IFBRANCH_M1 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
    bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
    bol (eqm (to (x2t 0)) (V 2));
    msg (pk 2, (e (b 1 11) 12, sign (sk 2) (ONE, e (b 1 11) 12)));
    bol
      (eqm (to (x3tft 0 1)) (V 1)) &
      (bacc (pk 3) (b 0 7) (r 8) (pi1 (x3tft 0 1))); 
    msg ok]) (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)));
   bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)));
   bol (eqm (to (x2t 1)) (V 2));
   msg (pk 2, (e (b 0 11) 12, sign (sk 2) (ONE, e (b 0 11) 12)));
   bol
     (eqm (to (x3tft 1 0)) (V 1)) &
     (bacc (pk 3) (b 1 7) (r 8) (pi1 (x3tft 1 0))); 
   msg ok]).
simpl.
pose proof( commit_swap (vt 0) (vt 1) _ 7 7 11 11 [ msg (sk 1); msg (sk 2); msg (r 8); msg (r 12); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1)); bol (eqm (to x1) (V 2))]); simpl in H.
assert( (L (vt 0)) # (L (vt 1))).
eapply len_f1; eapply len_nonce.
eapply EQmsg' in H0.
apply H in H0; clear H; rename H0 into H; try reflexivity.
appconst H.
x1checks x1 x1 H. simpl.
bterm 0 1 7 H.
funapp_vtrm 1 0 1 7 8 ONE H.
x1checks (x2t 0) (x2t 1) H.
bacctac 0 1 7 8 (x2t 0) (x2t 1) H.
funapptrmhyp (bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)))) 
(bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)))) H.
bterm 1 0 11 H.
funapp_vtrm 2 1 0 11 12 ONE H.

x1checks (x3tft 0 1) (x3tft 1 0) H. 
bacctac 0 1 7 8 (x3tft 0 1) (x3tft 1 0) H.
funapptrmhyp (bol (eqm (to (x3tft 0 1)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x3tft 0 1)))) (bol (eqm (to (x3tft 1 0)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x3tft 1 0)))) H.
x1checks (x4tftt 0 1) (x4tftt 1 0) H.
bacctac 1 0 11 12 (x4tftt 0 1) (x4tftt 1 0) H.
funapptrmhyp (bol (eqm (to (x4tftt 0 1)) (V 2)) & (bacc (pk 3) (b 1 11) (r 12) (pi2 (x4tftt 0 1)))) (bol (eqm (to (x4tftt 1 0)) (V 2)) & (bacc (pk 3) (b 0 11) (r 12) (pi2 (x4tftt 1 0)))) H.
restrsublis H.
(** subgoal *)
simpl.

pose proof( commit_swap (vt 0) (vt 1) _ 7 7 11 11 [ msg (sk 1); msg (sk 2); msg (r 8); msg (r 12); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1)); bol (eqm (to x1) (V 2))]); simpl in H.
assert( (L (vt 0)) # (L (vt 1))).
eapply len_f1; eapply len_nonce.
eapply EQmsg' in H0.
apply H in H0; clear H; rename H0 into H; try reflexivity.
appconst H.
x1checks x1 x1 H. simpl.
bterm 0 1 7 H.
funapp_vtrm 1 0 1 7 8 ONE H.
x1checks (x2t 0) (x2t 1) H.
bacctac 0 1 7 8 (x2t 0) (x2t 1) H.
funapptrmhyp (bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)))) 
(bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)))) H.
bterm 1 0 11 H.
funapp_vtrm 2 1 0 11 12 ONE H.

x1checks (x3tft 0 1) (x3tft 1 0) H. 
bacctac 0 1 7 8 (x3tft 0 1) (x3tft 1 0) H.
funapptrmhyp (bol (eqm (to (x3tft 0 1)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x3tft 0 1)))) (bol (eqm (to (x3tft 1 0)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x3tft 1 0)))) H.
x1checks (x4tftt 0 1) (x4tftt 1 0) H.
bacctac 1 0 11 12 (x4tftt 0 1) (x4tftt 1 0) H.
funapptrmhyp (bol (eqm (to (x4tftt 0 1)) (V 2)) & (bacc (pk 3) (b 1 11) (r 12) (pi2 (x4tftt 0 1)))) (bol (eqm (to (x4tftt 1 0)) (V 2)) & (bacc (pk 3) (b 0 11) (r 12) (pi2 (x4tftt 1 0)))) H.
restrsublis H.
(** subgoal *)
simpl. 
apply IFBRANCH_M2 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
    bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
    bol (eqm (to (x2t 0)) (V 2));
    msg (pk 2, (e (b 1 11) 12, sign (sk 2) (ONE, e (b 1 11) 12)));
    bol
      (eqm (to (x3tft 0 1)) (V 1)) &
      (bacc (pk 3) (b 0 7) (r 8) (pi1 (x3tft 0 1)))]) (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)));
   bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)));
   bol (eqm (to (x2t 1)) (V 2));
   msg (pk 2, (e (b 0 11) 12, sign (sk 2) (ONE, e (b 0 11) 12)));
   bol
     (eqm (to (x3tft 1 0)) (V 1)) &
     (bacc (pk 3) (b 1 7) (r 8) (pi1 (x3tft 1 0)))]).
simpl.
apply IFBRANCH_M1 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
    bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
    bol (eqm (to (x2t 0)) (V 2));
    msg (pk 2, (e (b 1 11) 12, sign (sk 2) (ONE, e (b 1 11) 12)));
    bol
      (eqm (to (x3tft 0 1)) (V 1)) &
      (bacc (pk 3) (b 0 7) (r 8) (pi1 (x3tft 0 1)));
    bol
      (eqm (to (x3tft 0 1)) (V 2)) &
      (bacc (pk 3) (b 1 11) (r 12) (pi2 (x3tft 0 1))); 
    msg ok]) (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)));
   bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)));
   bol (eqm (to (x2t 1)) (V 2));
   msg (pk 2, (e (b 0 11) 12, sign (sk 2) (ONE, e (b 0 11) 12)));
   bol
     (eqm (to (x3tft 1 0)) (V 1)) &
     (bacc (pk 3) (b 1 7) (r 8) (pi1 (x3tft 1 0)));
   bol
     (eqm (to (x3tft 1 0)) (V 2)) &
     (bacc (pk 3) (b 0 11) (r 12) (pi2 (x3tft 1 0))); 
   msg ok]). simpl.

pose proof( commit_swap (vt 0) (vt 1) _ 7 7 11 11 [ msg (sk 1); msg (sk 2); msg (r 8); msg (r 12); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1)); bol (eqm (to x1) (V 2))]); simpl in H.
assert( (L (vt 0)) # (L (vt 1))).
eapply len_f1; eapply len_nonce.
eapply EQmsg' in H0.
apply H in H0; clear H; rename H0 into H; try reflexivity.
appconst H.
x1checks x1 x1 H. simpl.
bterm 0 1 7 H.
funapp_vtrm 1 0 1 7 8 ONE H.
x1checks (x2t 0) (x2t 1) H.
bacctac 0 1 7 8 (x2t 0) (x2t 1) H.
funapptrmhyp (bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)))) 
(bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)))) H.
bterm 1 0 11 H.
funapp_vtrm 2 1 0 11 12 ONE H.

x1checks (x3tft 0 1) (x3tft 1 0) H. 
bacctac 0 1 7 8 (x3tft 0 1) (x3tft 1 0) H.
funapptrmhyp (bol (eqm (to (x3tft 0 1)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x3tft 0 1)))) (bol (eqm (to (x3tft 1 0)) (V 1))& (bacc (pk 3) (b 1 7) (r 8) (pi1 (x3tft 1 0)))) H.
bacctac 1 0 11 12 (x3tft 0 1) (x3tft 1 0) H.
funapptrmhyp (bol (eqm (to (x3tft 0 1)) (V 2)) & (bacc (pk 3) (b 1 11) (r 12) (pi2 (x3tft 0 1)))) (bol (eqm (to (x3tft 1 0)) (V 2)) & (bacc (pk 3) (b 0 11) (r 12) (pi2 (x3tft 1 0)))) H. 
x1checks (x4tftft 0 1) (x4tftft 1 0) H.
bacctac 0 1 7 8 (x4tftft 0 1) (x4tftft 1 0) H.   
funapptrmhyp (bol (eqm (to (x4tftft 0 1)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x4tftft 0 1)))) (bol (eqm (to (x4tftft 1 0)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x4tftft 1 0)))) H. 
restrsublis H. simpl. 
(** subgoal *)
pose proof( commit_swap (vt 0) (vt 1) _ 7 7 11 11 [ msg (sk 1); msg (sk 2); msg (r 8); msg (r 12); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1)); bol (eqm (to x1) (V 2))]); simpl in H.
assert( (L (vt 0)) # (L (vt 1))).
eapply len_f1; eapply len_nonce.
eapply EQmsg' in H0.
apply H in H0; clear H; rename H0 into H; try reflexivity.
appconst H.
x1checks x1 x1 H. simpl.
bterm 0 1 7 H.
funapp_vtrm 1 0 1 7 8 ONE H.
x1checks (x2t 0) (x2t 1) H.
bacctac 0 1 7 8 (x2t 0) (x2t 1) H. 
funapptrmhyp (bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)))) 
(bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)))) H.
bterm 1 0 11 H.
funapp_vtrm 2 1 0 11 12 ONE H.

x1checks (x3tft 0 1) (x3tft 1 0) H. 
bacctac 0 1 7 8 (x3tft 0 1) (x3tft 1 0) H.
funapptrmhyp (bol (eqm (to (x3tft 0 1)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x3tft 0 1)))) (bol (eqm (to (x3tft 1 0)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x3tft 1 0)))) H.
bacctac 1 0 11 12 (x3tft 0 1) (x3tft 1 0) H. 
 
funapptrmhyp (bol (eqm (to (x3tft 0 1)) (V 2)) & (bacc (pk 3) (b 1 11) (r 12) (pi2 (x3tft 0 1)))) (bol (eqm (to (x3tft 1 0)) (V 2)) & (bacc (pk 3) (b 0 11) (r 12) (pi2 (x3tft 1 0)))) H. 
x1checks (x4tftft 0 1) (x4tftft 1 0) H. 
bacctac 0 1 7 8 (x4tftft 0 1) (x4tftft 1 0) H.    
funapptrmhyp (bol (eqm (to (x4tftft 0 1)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x4tftft 0 1)))) (bol (eqm (to (x4tftft 1 0)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x4tftft 1 0)))) H. 
restrsublis H. simpl.
(** subgoal *) simpl.
pose proof( commit_swap (vt 0) (vt 1) _ 7 7 11 11 [ msg (sk 1); msg (sk 2); msg (r 8); msg (r 12); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1)); bol (eqm (to x1) (V 2))]); simpl in H.
assert( (L (vt 0)) # (L (vt 1))).
eapply len_f1; eapply len_nonce.
eapply EQmsg' in H0.
apply H in H0; clear H; rename H0 into H; try reflexivity.
appconst H.
x1checks x1 x1 H. simpl.
bterm 0 1 7 H.
funapp_vtrm 1 0 1 7 8 ONE H.
x1checks (x2t 0) (x2t 1) H.
bacctac 0 1 7 8 (x2t 0) (x2t 1) H. 
funapptrmhyp (bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)))) 
(bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)))) H.
bterm 1 0 11 H.
funapp_vtrm 2 1 0 11 12 ONE H.

x1checks (x3tft 0 1) (x3tft 1 0) H. 
bacctac 0 1 7 8 (x3tft 0 1) (x3tft 1 0) H.
funapptrmhyp (bol (eqm (to (x3tft 0 1)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x3tft 0 1)))) (bol (eqm (to (x3tft 1 0)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x3tft 1 0)))) H.
bacctac 1 0 11 12 (x3tft 0 1) (x3tft 1 0) H. 
 
funapptrmhyp (bol (eqm (to (x3tft 0 1)) (V 2)) & (bacc (pk 3) (b 1 11) (r 12) (pi2 (x3tft 0 1)))) (bol (eqm (to (x3tft 1 0)) (V 2)) & (bacc (pk 3) (b 0 11) (r 12) (pi2 (x3tft 1 0)))) H.
restrsublis H.
(** subgoal *)
simpl .
pose proof( commit_swap (vt 0) (vt 1) _ 7 7 11 11 [ msg (sk 1); msg (sk 2); msg (r 8); msg (r 12); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1)); bol (eqm (to x1) (V 2))]); simpl in H.
assert( (L (vt 0)) # (L (vt 1))).
eapply len_f1; eapply len_nonce.
eapply EQmsg' in H0.
apply H in H0; clear H; rename H0 into H; try reflexivity.
appconst H.
x1checks x1 x1 H. simpl.
bterm 0 1 7 H.
funapp_vtrm 1 0 1 7 8 ONE H.
x1checks (x2t 0) (x2t 1) H.
bacctac 0 1 7 8 (x2t 0) (x2t 1) H. 
funapptrmhyp (bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)))) 
(bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)))) H.
restrsublis H.
(** subgoal *)
simpl .
apply IFBRANCH_M4 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1))]) (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); 
                                                                        msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1))]).
simpl . repeat unfold q2.
apply IFBRANCH_M3 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
    bol (eqm (to x1) (V 2));
    msg (pk 2, (e (b 1 9) 10, sign (sk 2) (ONE, e (b 1 9) 10)))]) (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
   bol (eqm (to x1) (V 2));
   msg (pk 2, (e (b 0 9) 10, sign (sk 2) (ONE, e (b 0 9) 10)))]). simpl.
apply IFBRANCH_M2 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
    bol (eqm (to x1) (V 2));
    msg (pk 2, (e (b 1 9) 10, sign (sk 2) (ONE, e (b 1 9) 10)));
    bol
      (eqm (to (x2ft 1)) (V 2)) & (bacc (pk 3) (b 1 9) (r 10) (pi2 (x2ft 1)));
    msg ok]) (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
   bol (eqm (to x1) (V 2));
   msg (pk 2, (e (b 0 9) 10, sign (sk 2) (ONE, e (b 0 9) 10)));
   bol
     (eqm (to (x2ft 0)) (V 2)) & (bacc (pk 3) (b 0 9) (r 10) (pi2 (x2ft 0)));
   msg ok]). simpl .
apply IFBRANCH_M1 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
    bol (eqm (to x1) (V 2));
    msg (pk 2, (e (b 1 9) 10, sign (sk 2) (ONE, e (b 1 9) 10)));
    bol
      (eqm (to (x2ft 1)) (V 2)) & (bacc (pk 3) (b 1 9) (r 10) (pi2 (x2ft 1)));
    msg ok; bol (eqm (to (x3ftt 1)) (V 1));
    msg (pk 1, (e (b 0 23) 24, sign (sk 1) (ONE, e (b 0 23) 24)))]) (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
   bol (eqm (to x1) (V 2));
   msg (pk 2, (e (b 0 9) 10, sign (sk 2) (ONE, e (b 0 9) 10)));
   bol
     (eqm (to (x2ft 0)) (V 2)) & (bacc (pk 3) (b 0 9) (r 10) (pi2 (x2ft 0)));
   msg ok; bol (eqm (to (x3ftt 0)) (V 1));
   msg (pk 1, (e (b 1 23) 24, sign (sk 1) (ONE, e (b 1 23) 24)))]). simpl.
pose proof( commit_swap (vt 1) (vt 0) _ 9 9 23 23 [ msg (sk 1); msg (sk 2); msg (r 10); msg (r 24); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1)); bol (eqm (to x1) (V 2))]); simpl in H.
assert( (L (vt 1)) # (L (vt 0))).
eapply len_f1; eapply len_nonce.
eapply EQmsg' in H0.
apply H in H0; clear H; rename H0 into H; try reflexivity.
appconst H.
x1checks x1 x1 H. simpl.
bterm 1 0 9 H.
funapp_vtrm 2 1 0 9 10 ONE H. 
x1checks (x2ft 1) (x2ft 0) H.
bacctac 1 0 9 10 (x2ft 1) (x2ft 0) H.  
funapptrmhyp (bol (eqm (to (x2ft 1)) (V 2)) & (bacc (pk 3) (b 1 9) (r 10) (pi2 (x2ft 1)))) (bol (eqm (to (x2ft 0)) (V 2)) & (bacc (pk 3) (b 0 9) (r 10) (pi2 (x2ft 0)))) H.
x1checks (x3ftt 1) (x3ftt 0) H.
bterm 0 1 23 H.
funapp_vtrm 1 0 1 23 24 ONE H.
x1checks (x4fttt 0 1) (x4fttt 1 0) H.
bacctac 0 1 23 24 (x4fttt 0 1) (x4fttt 1 0) H.
funapptrmhyp (bol (eqm (to (x4fttt 0 1)) (V 1)) & (bacc (pk 3) (b 0 23) (r 24) (pi1 (x4fttt 0 1)))) (bol (eqm (to (x4fttt 1 0)) (V 1)) & (bacc (pk 3) (b 1 23) (r 24) (pi1 (x4fttt 1 0)))) H.
restrsublis H.
(** subgoal *) simpl. 
pose proof( commit_swap (vt 1) (vt 0) _ 9 9 23 23 [ msg (sk 1); msg (sk 2); msg (r 10); msg (r 24); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1)); bol (eqm (to x1) (V 2))]); simpl in H.
assert( (L (vt 1)) # (L (vt 0))).
eapply len_f1; eapply len_nonce.
eapply EQmsg' in H0.
apply H in H0; clear H; rename H0 into H; try reflexivity.
appconst H.
x1checks x1 x1 H. simpl.
bterm 1 0 9 H.
funapp_vtrm 2 1 0 9 10 ONE H. 
x1checks (x2ft 1) (x2ft 0) H.
bacctac 1 0 9 10 (x2ft 1) (x2ft 0) H.  
funapptrmhyp (bol (eqm (to (x2ft 1)) (V 2)) & (bacc (pk 3) (b 1 9) (r 10) (pi2 (x2ft 1)))) (bol (eqm (to (x2ft 0)) (V 2)) & (bacc (pk 3) (b 0 9) (r 10) (pi2 (x2ft 0)))) H.
x1checks (x3ftt 1) (x3ftt 0) H.
bterm 0 1 23 H.
funapp_vtrm 1 0 1 23 24 ONE H.
x1checks (x4fttt 0 1) (x4fttt 1 0) H.
bacctac 0 1 23 24 (x4fttt 0 1) (x4fttt 1 0) H.
funapptrmhyp (bol (eqm (to (x4fttt 0 1)) (V 1)) & (bacc (pk 3) (b 0 23) (r 24) (pi1 (x4fttt 0 1)))) (bol (eqm (to (x4fttt 1 0)) (V 1)) & (bacc (pk 3) (b 1 23) (r 24) (pi1 (x4fttt 1 0)))) H. 
restrsublis H.
(** subgoal *)
simpl. 
pose proof( commit_swap (vt 1) (vt 0) _ 9 9 23 23 [ msg (sk 1); msg (sk 2); msg (r 10); msg (r 24); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1)); bol (eqm (to x1) (V 2))]); simpl in H.
assert( (L (vt 1)) # (L (vt 0))).
eapply len_f1; eapply len_nonce.
eapply EQmsg' in H0.
apply H in H0; clear H; rename H0 into H; try reflexivity.
appconst H.
x1checks x1 x1 H. simpl.
bterm 1 0 9 H.
funapp_vtrm 2 1 0 9 10 ONE H. 
x1checks (x2ft 1) (x2ft 0) H.
bacctac 1 0 9 10 (x2ft 1) (x2ft 0) H.  
funapptrmhyp (bol (eqm (to (x2ft 1)) (V 2)) & (bacc (pk 3) (b 1 9) (r 10) (pi2 (x2ft 1)))) (bol (eqm (to (x2ft 0)) (V 2)) & (bacc (pk 3) (b 0 9) (r 10) (pi2 (x2ft 0)))) H.
x1checks (x3ftt 1) (x3ftt 0) H.
restrsublis H.
(** subgoal *)
simpl.
apply IFBRANCH_M3 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
    bol (eqm (to x1) (V 2));
    msg (pk 2, (e (b 1 9) 10, sign (sk 2) (ONE, e (b 1 9) 10)));
    bol
      (eqm (to (x2ft 1)) (V 2)) & (bacc (pk 3) (b 1 9) (r 10) (pi2 (x2ft 1)))]) (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
   bol (eqm (to x1) (V 2));
   msg (pk 2, (e (b 0 9) 10, sign (sk 2) (ONE, e (b 0 9) 10)));
   bol
     (eqm (to (x2ft 0)) (V 2)) & (bacc (pk 3) (b 0 9) (r 10) (pi2 (x2ft 0)))]).
simpl. 
apply IFBRANCH_M2 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
    bol (eqm (to x1) (V 2));
    msg (pk 2, (e (b 1 9) 10, sign (sk 2) (ONE, e (b 1 9) 10)));
    bol
      (eqm (to (x2ft 1)) (V 2)) & (bacc (pk 3) (b 1 9) (r 10) (pi2 (x2ft 1)));
    bol (eqm (to (x2ft 1)) (V 1));
    msg (pk 1, (e (b 0 13) 14, sign (sk 1) (ONE, e (b 0 13) 14)))])(ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
   bol (eqm (to x1) (V 2));
   msg (pk 2, (e (b 0 9) 10, sign (sk 2) (ONE, e (b 0 9) 10)));
   bol
     (eqm (to (x2ft 0)) (V 2)) & (bacc (pk 3) (b 0 9) (r 10) (pi2 (x2ft 0)));
   bol (eqm (to (x2ft 0)) (V 1));
   msg (pk 1, (e (b 1 13) 14, sign (sk 1) (ONE, e (b 1 13) 14)))]).
simpl. 
apply IFBRANCH_M1 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
    bol (eqm (to x1) (V 2));
    msg (pk 2, (e (b 1 9) 10, sign (sk 2) (ONE, e (b 1 9) 10)));
    bol
      (eqm (to (x2ft 1)) (V 2)) & (bacc (pk 3) (b 1 9) (r 10) (pi2 (x2ft 1)));
    bol (eqm (to (x2ft 1)) (V 1));
    msg (pk 1, (e (b 0 13) 14, sign (sk 1) (ONE, e (b 0 13) 14)));
    bol
      (eqm (to (x3ftft 0 1)) (V 1)) &
      (bacc (pk 3) (b 0 13) (r 14) (pi1 (x3ftft 0 1))); 
    msg ok])(ml2:=  [msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
   bol (eqm (to x1) (V 2));
   msg (pk 2, (e (b 0 9) 10, sign (sk 2) (ONE, e (b 0 9) 10)));
   bol
     (eqm (to (x2ft 0)) (V 2)) & (bacc (pk 3) (b 0 9) (r 10) (pi2 (x2ft 0)));
   bol (eqm (to (x2ft 0)) (V 1));
   msg (pk 1, (e (b 1 13) 14, sign (sk 1) (ONE, e (b 1 13) 14)));
   bol
     (eqm (to (x3ftft 1 0)) (V 1)) &
     (bacc (pk 3) (b 1 13) (r 14) (pi1 (x3ftft 1 0))); 
   msg ok]).
simpl. 
pose proof( commit_swap (vt 1) (vt 0) _ 9 9 13 13 [ msg (sk 1); msg (sk 2); msg (r 10); msg (r 14); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1)); bol (eqm (to x1) (V 2))]); simpl in H.
assert( (L (vt 1)) # (L (vt 0))).
eapply len_f1; eapply len_nonce.
eapply EQmsg' in H0.
apply H in H0; clear H; rename H0 into H; try reflexivity.
appconst H.
x1checks x1 x1 H. simpl.
bterm 1 0 9 H.
funapp_vtrm 2 1 0 9 10 ONE H. 
x1checks (x2ft 1) (x2ft 0) H.
bacctac 1 0 9 10 (x2ft 1) (x2ft 0) H.   simpl. 
bterm 0 1 13 H.
funapp_vtrm 1 0 1 13 14 ONE H.
x1checks (x3ftft 0 1) (x3ftft 1 0) H. 
funapptrmhyp (bol (eqm (to (x2ft 1)) (V 2)) & (bacc (pk 3) (b 1 9) (r 10) (pi2 (x2ft 1)))) (bol (eqm (to (x2ft 0)) (V 2)) & (bacc (pk 3) (b 0 9) (r 10) (pi2 (x2ft 0)))) H. 
bacctac 0 1 13 14 (x3ftft 0 1) (x3ftft 1 0) H.
x1checks (x4ftftt 0 1) (x4ftftt 1 0) H. 
bacctac 1 0 9 10 (x4ftftt 0 1) (x4ftftt 1 0) H. 

funapptrmhyp (bol (eqm (to (x3ftft 0 1)) (V 1)) & (bacc (pk 3) (b 0 13) (r 14) (pi1 (x3ftft 0 1)))) (bol (eqm (to (x3ftft 1 0)) (V 1)) &
     (bacc (pk 3) (b 1 13) (r 14) (pi1 (x3ftft 1 0)))) H.
funapptrmhyp (bol (eqm (to (x4ftftt 0 1)) (V 2)) & (bacc (pk 3) (b 1 9) (r 10) (pi2 (x4ftftt 0 1)))) (bol (eqm (to (x4ftftt 1 0)) (V 2)) & (bacc (pk 3) (b 0 9) (r 10) (pi2 (x4ftftt 1 0)))) H.
restrsublis H.
(** subgoal *)
simpl. 
pose proof( commit_swap (vt 1) (vt 0) _ 9 9 13 13 [ msg (sk 1); msg (sk 2); msg (r 10); msg (r 14); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1)); bol (eqm (to x1) (V 2))]); simpl in H.
assert( (L (vt 1)) # (L (vt 0))).
eapply len_f1; eapply len_nonce.
eapply EQmsg' in H0.
apply H in H0; clear H; rename H0 into H; try reflexivity.
appconst H.
x1checks x1 x1 H. simpl.
bterm 1 0 9 H.
funapp_vtrm 2 1 0 9 10 ONE H. 
x1checks (x2ft 1) (x2ft 0) H.
bacctac 1 0 9 10 (x2ft 1) (x2ft 0) H.    simpl. 
bterm 0 1 13 H.
funapp_vtrm 1 0 1 13 14 ONE H.
x1checks (x3ftft 0 1) (x3ftft 1 0) H. 
funapptrmhyp (bol (eqm (to (x2ft 1)) (V 2)) & (bacc (pk 3) (b 1 9) (r 10) (pi2 (x2ft 1)))) (bol (eqm (to (x2ft 0)) (V 2)) & (bacc (pk 3) (b 0 9) (r 10) (pi2 (x2ft 0)))) H. 
bacctac 0 1 13 14 (x3ftft 0 1) (x3ftft 1 0) H.
x1checks (x4ftftt 0 1) (x4ftftt 1 0) H. 
bacctac 1 0 9 10 (x4ftftt 0 1) (x4ftftt 1 0) H. 

funapptrmhyp (bol (eqm (to (x3ftft 0 1)) (V 1)) & (bacc (pk 3) (b 0 13) (r 14) (pi1 (x3ftft 0 1)))) (bol (eqm (to (x3ftft 1 0)) (V 1)) &
     (bacc (pk 3) (b 1 13) (r 14) (pi1 (x3ftft 1 0)))) H.
funapptrmhyp (bol (eqm (to (x4ftftt 0 1)) (V 2)) & (bacc (pk 3) (b 1 9) (r 10) (pi2 (x4ftftt 0 1)))) (bol (eqm (to (x4ftftt 1 0)) (V 2)) & (bacc (pk 3) (b 0 9) (r 10) (pi2 (x4ftftt 1 0)))) H.
restrsublis H.
(** subgoal *)
simpl .
apply IFBRANCH_M2 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
    bol (eqm (to x1) (V 2));
    msg (pk 2, (e (b 1 9) 10, sign (sk 2) (ONE, e (b 1 9) 10)));
    bol
      (eqm (to (x2ft 1)) (V 2)) & (bacc (pk 3) (b 1 9) (r 10) (pi2 (x2ft 1)));
    bol (eqm (to (x2ft 1)) (V 1));
    msg (pk 1, (e (b 0 13) 14, sign (sk 1) (ONE, e (b 0 13) 14)));
    bol
      (eqm (to (x3ftft 0 1)) (V 1)) &
      (bacc (pk 3) (b 0 13) (r 14) (pi1 (x3ftft 0 1)))]) (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
   bol (eqm (to x1) (V 2));
   msg (pk 2, (e (b 0 9) 10, sign (sk 2) (ONE, e (b 0 9) 10)));
   bol
     (eqm (to (x2ft 0)) (V 2)) & (bacc (pk 3) (b 0 9) (r 10) (pi2 (x2ft 0)));
   bol (eqm (to (x2ft 0)) (V 1));
   msg (pk 1, (e (b 1 13) 14, sign (sk 1) (ONE, e (b 1 13) 14)));
   bol
     (eqm (to (x3ftft 1 0)) (V 1)) &
     (bacc (pk 3) (b 1 13) (r 14) (pi1 (x3ftft 1 0)))]).
simpl .
apply IFBRANCH_M1 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
    bol (eqm (to x1) (V 2));
    msg (pk 2, (e (b 1 9) 10, sign (sk 2) (ONE, e (b 1 9) 10)));
    bol
      (eqm (to (x2ft 1)) (V 2)) & (bacc (pk 3) (b 1 9) (r 10) (pi2 (x2ft 1)));
    bol (eqm (to (x2ft 1)) (V 1));
    msg (pk 1, (e (b 0 13) 14, sign (sk 1) (ONE, e (b 0 13) 14)));
    bol
      (eqm (to (x3ftft 0 1)) (V 1)) &
      (bacc (pk 3) (b 0 13) (r 14) (pi1 (x3ftft 0 1)));
    bol
      (eqm (to (x3ftft 0 1)) (V 2)) &
      (bacc (pk 3) (b 1 9) (r 10) (pi2 (x3ftft 0 1))); 
    msg ok]) (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
   bol (eqm (to x1) (V 2));
   msg (pk 2, (e (b 0 9) 10, sign (sk 2) (ONE, e (b 0 9) 10)));
   bol
     (eqm (to (x2ft 0)) (V 2)) & (bacc (pk 3) (b 0 9) (r 10) (pi2 (x2ft 0)));
   bol (eqm (to (x2ft 0)) (V 1));
   msg (pk 1, (e (b 1 13) 14, sign (sk 1) (ONE, e (b 1 13) 14)));
   bol
     (eqm (to (x3ftft 1 0)) (V 1)) &
     (bacc (pk 3) (b 1 13) (r 14) (pi1 (x3ftft 1 0)));
   bol
     (eqm (to (x3ftft 1 0)) (V 2)) &
     (bacc (pk 3) (b 0 9) (r 10) (pi2 (x3ftft 1 0))); 
   msg ok]). simpl .
pose proof( commit_swap (vt 1) (vt 0) _ 9 9 13 13 [ msg (sk 1); msg (sk 2); msg (r 10); msg (r 14); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1)); bol (eqm (to x1) (V 2))]); simpl in H.
assert( (L (vt 1)) # (L (vt 0))).
eapply len_f1; eapply len_nonce.
eapply EQmsg' in H0.
apply H in H0; clear H; rename H0 into H; try reflexivity.
appconst H.
x1checks x1 x1 H. simpl.
bterm 1 0 9 H.
funapp_vtrm 2 1 0 9 10 ONE H. 
x1checks (x2ft 1) (x2ft 0) H.
bacctac 1 0 9 10 (x2ft 1) (x2ft 0) H.    simpl. 
bterm 0 1 13 H.
funapp_vtrm 1 0 1 13 14 ONE H.
x1checks (x3ftft 0 1) (x3ftft 1 0) H. 
funapptrmhyp (bol (eqm (to (x2ft 1)) (V 2)) & (bacc (pk 3) (b 1 9) (r 10) (pi2 (x2ft 1)))) (bol (eqm (to (x2ft 0)) (V 2)) & (bacc (pk 3) (b 0 9) (r 10) (pi2 (x2ft 0)))) H. 
bacctac 0 1 13 14 (x3ftft 0 1) (x3ftft 1 0) H.

funapptrmhyp (bol (eqm (to (x3ftft 0 1)) (V 1)) & (bacc (pk 3) (b 0 13) (r 14) (pi1 (x3ftft 0 1)))) (bol (eqm (to (x3ftft 1 0)) (V 1)) &
                                                                                                         (bacc (pk 3) (b 1 13) (r 14) (pi1 (x3ftft 1 0)))) H.
bacctac 1 0 9 10 (x3ftft 0 1) (x3ftft 1 0) H.
funapptrmhyp (bol (eqm (to (x3ftft 0 1)) (V 2)) & (bacc (pk 3) (b 1 9) (r 10) (pi2 (x3ftft 0 1)))) (bol (eqm (to (x3ftft 1 0)) (V 2)) & (bacc (pk 3) (b 0 9) (r 10) (pi2 (x3ftft 1 0)))) H.
x1checks (x4ftftft 0 1) (x4ftftft 1 0) H.  
bacctac 0 1 13 14 (x4ftftft 0 1) (x4ftftft 1 0) H. 
 
funapptrmhyp (bol (eqm (to (x4ftftft 0 1)) (V 1)) & (bacc (pk 3) (b 0 13) (r 14) (pi1 (x4ftftft 0 1)))) (bol (eqm (to (x4ftftft 1 0)) (V 1)) & (bacc (pk 3) (b 1 13) (r 14) (pi1 (x4ftftft 1 0)))) H.
restrsublis H.
(** subgoal *)
pose proof( commit_swap (vt 1) (vt 0) _ 9 9 13 13 [ msg (sk 1); msg (sk 2); msg (r 10); msg (r 14); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1)); bol (eqm (to x1) (V 2))]); simpl in H.
assert( (L (vt 1)) # (L (vt 0))).
eapply len_f1; eapply len_nonce.
eapply EQmsg' in H0.
apply H in H0; clear H; rename H0 into H; try reflexivity.
appconst H.
x1checks x1 x1 H. simpl.
bterm 1 0 9 H.
funapp_vtrm 2 1 0 9 10 ONE H. 
x1checks (x2ft 1) (x2ft 0) H.
bacctac 1 0 9 10 (x2ft 1) (x2ft 0) H.    simpl. 
bterm 0 1 13 H.
funapp_vtrm 1 0 1 13 14 ONE H.
x1checks (x3ftft 0 1) (x3ftft 1 0) H. 
funapptrmhyp (bol (eqm (to (x2ft 1)) (V 2)) & (bacc (pk 3) (b 1 9) (r 10) (pi2 (x2ft 1)))) (bol (eqm (to (x2ft 0)) (V 2)) & (bacc (pk 3) (b 0 9) (r 10) (pi2 (x2ft 0)))) H. 
bacctac 0 1 13 14 (x3ftft 0 1) (x3ftft 1 0) H.

funapptrmhyp (bol (eqm (to (x3ftft 0 1)) (V 1)) & (bacc (pk 3) (b 0 13) (r 14) (pi1 (x3ftft 0 1)))) (bol (eqm (to (x3ftft 1 0)) (V 1)) &
                                                                                                         (bacc (pk 3) (b 1 13) (r 14) (pi1 (x3ftft 1 0)))) H.
bacctac 1 0 9 10 (x3ftft 0 1) (x3ftft 1 0) H.
funapptrmhyp (bol (eqm (to (x3ftft 0 1)) (V 2)) & (bacc (pk 3) (b 1 9) (r 10) (pi2 (x3ftft 0 1)))) (bol (eqm (to (x3ftft 1 0)) (V 2)) & (bacc (pk 3) (b 0 9) (r 10) (pi2 (x3ftft 1 0)))) H.
x1checks (x4ftftft 0 1) (x4ftftft 1 0) H.  
bacctac 0 1 13 14 (x4ftftft 0 1) (x4ftftft 1 0) H. 
 
funapptrmhyp (bol (eqm (to (x4ftftft 0 1)) (V 1)) & (bacc (pk 3) (b 0 13) (r 14) (pi1 (x4ftftft 0 1)))) (bol (eqm (to (x4ftftft 1 0)) (V 1)) & (bacc (pk 3) (b 1 13) (r 14) (pi1 (x4ftftft 1 0)))) H.
restrsublis H.
(** subgoal *)
simpl.
pose proof( commit_swap (vt 1) (vt 0) _ 9 9 13 13 [ msg (sk 1); msg (sk 2); msg (r 10); msg (r 14); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1)); bol (eqm (to x1) (V 2))]); simpl in H.
assert( (L (vt 1)) # (L (vt 0))).
eapply len_f1; eapply len_nonce.
eapply EQmsg' in H0.
apply H in H0; clear H; rename H0 into H; try reflexivity.
appconst H.
x1checks x1 x1 H. simpl.
bterm 1 0 9 H.
funapp_vtrm 2 1 0 9 10 ONE H. 
x1checks (x2ft 1) (x2ft 0) H.
bacctac 1 0 9 10 (x2ft 1) (x2ft 0) H.    simpl. 
bterm 0 1 13 H.
funapp_vtrm 1 0 1 13 14 ONE H.
x1checks (x3ftft 0 1) (x3ftft 1 0) H. 
funapptrmhyp (bol (eqm (to (x2ft 1)) (V 2)) & (bacc (pk 3) (b 1 9) (r 10) (pi2 (x2ft 1)))) (bol (eqm (to (x2ft 0)) (V 2)) & (bacc (pk 3) (b 0 9) (r 10) (pi2 (x2ft 0)))) H.  
bacctac 0 1 13 14 (x3ftft 0 1) (x3ftft 1 0) H.

funapptrmhyp (bol (eqm (to (x3ftft 0 1)) (V 1)) & (bacc (pk 3) (b 0 13) (r 14) (pi1 (x3ftft 0 1)))) (bol (eqm (to (x3ftft 1 0)) (V 1)) &
                                                                                                         (bacc (pk 3) (b 1 13) (r 14) (pi1 (x3ftft 1 0)))) H. 
bacctac 1 0 9 10 (x3ftft 0 1) (x3ftft 1 0) H.
funapptrmhyp (bol (eqm (to (x3ftft 0 1)) (V 2)) & (bacc (pk 3) (b 1 9) (r 10) (pi2 (x3ftft 0 1)))) (bol (eqm (to (x3ftft 1 0)) (V 2)) & (bacc (pk 3) (b 0 9) (r 10) (pi2 (x3ftft 1 0)))) H.

restrsublis H . simpl.
pose proof(commit_ind (vt 1) (vt 0) _ 9 9 [ msg (sk 1); msg (sk 2); msg (r 10); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1))]) ; try reflexivity; simpl in H.
assert( (L (vt 1)) # (L (vt 0))).
eapply len_f1; eapply len_nonce. simpl. 
eapply EQmsg' in H0.
apply H in H0; clear H; rename H0 into H; try reflexivity.
funapptrmhyp (msg (blind (commit (v (N 1)) (r 9)) (pk 3) (r 10))) (msg (blind (commit (v (N 0)) (r 9)) (pk 3) (r 10))) H.  
 appconst H. 
x1checks x1 x1 H. 
funapp_vtrm 2 1 0 9 10 ONE H. simpl.  
x1checks (x2ft 1) (x2ft 0) H.  
bacctac 1 0 9 10 (x2ft 1) (x2ft 0) H.
funapptrmhyp (bol (eqm (to (x2ft 1)) (V 2)) & (bacc (pk 3) (b 1 9) (r 10) (pi2 (x2ft 1)))) (bol (eqm (to (x2ft 0)) (V 2)) & (bacc (pk 3) (b 0 9) (r 10) (pi2 (x2ft 0)))) H.
restrsublis H. simpl .
(** subgoal *)
reflexivity.
Qed.


Theorem frame3ind: (phi3 0 1) ~ (phi3 1 0).
Proof. pose proof(frame4ind).  unfold phi4 in H. simpl in H. restrproj_in 10 H.  assumption. Qed.

Theorem frame2ind: (phi2 0 1) ~ (phi2 1 0).
Proof. pose proof(frame3ind). unfold phi3 in H; simpl in H; restrproj_in 9 H; try assumption. Qed.

Theorem frame1ind: (phi1 0 1) ~ (phi1 1 0).
Proof. pose proof(frame2ind). unfold phi2 in H; simpl in H; restrproj_in 8 H; try assumption. Qed.