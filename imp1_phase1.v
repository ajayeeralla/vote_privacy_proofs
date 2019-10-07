Load "foo_imp1".
    
Theorem frame2ind: (phi2 0 1) ~ (phi2 1 0).
Proof. repeat unfold phi2, phi1. simpl. repeat unfold t1. repeat unfold q0, q1, q2. 
      
(** apply IFBRANCH *)
apply IFBRANCH_M2 with (ml1:= phi0) (ml2:= phi0).
 simpl.
 repeat apply IFBRANCH_M1 with (ml1:=[msg (pk 1); msg (pk 2); msg (pk 5); msg pkat; 
    msg (vt 0); msg (vt 1); bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8) (r 30)))] ) (ml2:=  [msg (pk 1); msg (pk 2); msg (pk 5); msg pkat; msg (vt 0); 
   msg (vt 1); bol (eqm (to x1) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (e (b 1 7) 8) (r 30)))]);
    
(** subgoal 1 *)  
   pose proof( commit_swap (vt 0) (vt 1) _ 7 7 11 11 [ msg (sk 1); msg (sk 2); msg (r 8); msg (r 12); msg (r 30); msg (r 32); msg (pk 1); msg (pk 2); msg (pk 5); msg pkat; msg (vt 0); msg (vt 1); bol (eqm (to x1) (V 1))]); simpl in H;
assert( (L (vt 0)) # (L (vt 1)));
try eapply len_f1; try eapply len_nonce;
eapply EQmsg' in H0; 
apply H in H0; clear H; rename H0 into H; auto.
appconst H;
x1checks x1 x1 H; simpl;
bterm 0 1 7 H;
(** Appending triple term of voter1 on both sides *) 
funapptrmhyp (msg (sign (sk 1) (e (b 0 7) 8) (r 30))) (msg (sign (sk 1) (e (b 1 7) 8) (r 30))) H;
(*funapptrmhyp (msg ((e (b 0 7) 8), (sign (sk 1) (e (b 0 7) 8) (r 30)))) (msg ((e (b 1 7) 8),  (sign (sk 1) (e (b 1 7) 8) (r 30)))) H; *)
funapptrmhyp (msg (pk 1, (e (b 0 7) 8), (sign (sk 1) (e (b 0 7) 8) (r 30)))) (msg (pk 1, (e (b 1 7) 8), (sign (sk 1) (e (b 1 7) 8) (r 30)))) H;
x1checks (x2t 0) (x2t 1) H.
(** Appending second blind term *)
bterm 1 0 11 H;
(** Appending triple term of voter2 on both sides *)  
funapptrmhyp (msg (sign (sk 2) (e (b 1 11) 12) (r 32))) (msg (sign (sk 2) (e (b 0 11) 12) (r 32))) H;
(*funapptrmhyp (msg ((e (b 1 11) 12), (sign (sk 2) (e (b 1 11) 12) (r 32)))) (msg ((e (b 0 11) 12),  (sign (sk 2) (e (b 0 11) 12) (r 32)))) H; *)
funapptrmhyp (msg (pk 2, (e (b 1 11) 12), (sign (sk 2) (e (b 1 11) 12) (r 32)))) (msg (pk 2, (e (b 0 11) 12), (sign (sk 2) (e (b 0 11) 12) (r 32)))) H.
(** Reduce goal if hypothesis redundantly contain goal *)
restrsublis H.
Eval compute in (conv_mylist_listos
        [msg (pk 1); msg (pk 2); msg (pk 5); msg pkat; 
        msg (vt 0); msg (vt 1); bol (eqm (to x1) (V 1));
        msg (pk 1, e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8) (r 30));
        msg
          (ifm (eqm (to (x2t 0)) (V 2))
               (pk 2, e (b 1 11) 12, sign (sk 2) (e (b 1 11) 12) (r 32)) O)]).
SearchAbout checksublis'.
(** goal-3 *)  
apply IFBRANCH_M2 with (ml1:= (phi0 ++ [bol (eqm (to x1) (V 1))])) (ml2:= (phi0 ++ [bol (eqm (to x1) (V 1))]));simpl.
                                                                                                                 repeat (apply IFBRANCH_M1 with (ml1:= (phi0 ++ [bol (eqm (to x1) (V 1)); bol (eqm (to x1) (V 2));
    msg (pk 2, (e (b 1 9) 10, sign (sk 2) (e (b 1 9) 10) (r 31)))])) (ml2:= (phi0 ++ [bol (eqm (to x1) (V 1)); bol (eqm (to x1) (V 2));
    msg (pk 2, (e (b 0 9) 10, sign (sk 2) (e (b 0 9) 10) (r 31)))]));  
 pose proof( commit_swap (vt 1) (vt 0) _ 9 9 13 13 [ msg (sk 1); msg (sk 2); msg (r 10); msg (r 14); msg (r 31); msg (r 33); msg (pk 1); msg (pk 2); msg (pk 5); msg pkat; msg (vt 0); msg (vt 1); bol (eqm (to x1) (V 1));  bol (eqm (to x1) (V 2))]); simpl in H;
assert( (L (vt 1)) # (L (vt 0)));
try eapply len_f1;  try eapply len_nonce;
eapply EQmsg' in H0;
apply H in H0; clear H; rename H0 into H; auto;
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
Theorem frame1ind: (phi1 0 1) ~ (phi1 1 0).
Proof. pose proof(frame2ind). unfold phi2 in H; simpl in H; restrproj_in 8 H; try assumption. Qed.