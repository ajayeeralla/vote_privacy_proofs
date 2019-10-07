 Load "phase23". 
 Theorem eq_true: forall t, (eqm t t) ## TRue.
   Proof. intros.
apply EQmsg'.
reflexivity.
Qed.
 
Axiom pair_eq: forall t1 t2 t3 t4, (eqm (t1, t2) (t3, t4)) ## (eqm t1 t3) & (eqm t2 t4).

Axiom eq_sym: forall t1 t2 , (eqm t1 t2) ## (eqm t2 t1).
Axiom oTwoneq: (eqm ONE TWO) ## FAlse.
Axiom oThreeneq: (eqm ONE THREE) ## FAlse.
Axiom tThreeneq: (eqm TWO THREE) ## FAlse.
Ltac aply_pair_eq :=
  match goal with
    |[|- context[(eqm (?X1, ?X2) (?X3, ?X4))] ] => rewrite pair_eq with (t1:= X1) (t2:= X2) (t3:= X3) (t4:= X4)
  end.


Axiom eqbr_ver: forall t1 t2 t3 t4 t5 t6 b1 b2 b3, (ifm (ifb (ifb b1  (ifb (eqm t1 t2) b2 FAlse) FAlse)   (ifb (eqm t3 t4) b3 FAlse) FAlse) t5 t6) # (ifm (ifb (ifb b1  (ifb (eqm t1 t2) b2 FAlse) FAlse)   (ifb (eqm t3 t4) b3 FAlse) FAlse)  (submsg_msg' t3 t4 (submsg_msg' t1 t2 t5)) t6).
Ltac aply_eqbr_ver t :=
  match goal with
    | [|- context [(ifm (ifb (ifb ?B1 (ifb (eqm t ?T2) ?B2 FAlse) FAlse) (ifb (eqm ?T3 ?T4) ?B3 FAlse) FAlse) ?T5 ?T6)] ] =>
      rewrite eqbr_ver with (b1:= B1) (b2:= B2) (b3:= B3) (t1:= t) (t2:= T2) (t3:= T3) (t4:= T4) (t5:= T5) (t6:= T6)
  end.

Axiom dep_enc :  forall(n:nat) (x z :message), (dec (enc x (pk n) z) (sk n)) # x.
Theorem frame7ind: (phi7 0 1) ~ (phi7 1 0).
Proof. repeat unfold phi7, phi6, phi5, phi4, phi3, phi2, phi1. simpl.
       repeat unfold q0, t1, t2, t3, t4, t5, t6. simpl.
       repeat unfold q1, q2, q1_s, q2_s, q1_ss, q2_ss, q1_ss', q2_ss', q1_ss'', q2_ss'', q1_ss''', q2_ss'''.
       apply IFBRANCH_M7 with (ml1:= phi0) (ml2:= phi0).
       simpl.  
       apply IFBRANCH_M6 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
                                      msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
                                      msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)))])
                                (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1)); msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)))]). simpl.
       repeat unfold q11, q11_s, q11_s', q11_s'', q11_s'''.
       repeat unfold q111, qs111, qs'111, qs''111.
       apply IFBRANCH_M5 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
                                      msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
                                      msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
                                      bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
                                      msg ok]) (ml2:=  [msg (pk 1); msg (pk 2); msg (pk 3); 
                                                        msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
                                                        msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)));
                                                        bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)));
                                                        msg ok]). simpl.
       
       apply IFBRANCH_M4 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
                                      msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
                                      msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
                                      bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
                                      msg ok; bol (eqm (to (x3tt 0)) (V 2));
                                      msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)))])
                                (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); 
                                        msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
                                        msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)));
                                        bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)));
                                        msg ok; bol (eqm (to (x3tt 1)) (V 2));
                                        msg (pk 2, (e (b 0 19) 20, sign (sk 2) (ONE, e (b 0 19) 20)))]). simpl.
       repeat unfold q111v1, q111v2, q111m. repeat unfold vtrm, voter1, voter2, mnetop.
       apply IFBRANCH_M3 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
                                      msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
                                      msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
                                      bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
                                      msg ok; bol (eqm (to (x3tt 0)) (V 2));
                                      msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)));
                                      bol (eqm (to (x4ttt 0 1)) (V 2)) & (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1))); 
                                      msg ok])(ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); 
                                                      msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
                                                      msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)));
                                                      bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)));
                                                      msg ok; bol (eqm (to (x3tt 1)) (V 2));
                                                      msg (pk 2, (e (b 0 19) 20, sign (sk 2) (ONE, e (b 0 19) 20)));
                                                      bol
                                                        (eqm (to (x4ttt 1 0)) (V 2)) &
                                                        (bacc (pk 3) (b 0 19) (r 20) (pi2 (x4ttt 1 0))); 
                                                      msg ok]). simpl.
       
       apply IFBRANCH_M2 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
                                      msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
                                      msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
                                      bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
                                      msg ok; bol (eqm (to (x3tt 0)) (V 2));
                                      msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)));
                                      bol (eqm (to (x4ttt 0 1)) (V 2)) & (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1))); 
                                      msg ok; bol (eqm (to (x54t 0 1)) (V 1));
                                      msg
                                        (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (r 25),
                                         sign (sk 1)
                                              (TWO, enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (r 25)))])
                                (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); msg (pk 5); msg (N 6);
                                        bol (eqm (to x1) (V 1));  msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)));
                                        bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)));
                                        msg ok; bol (eqm (to (x3tt 1)) (V 2));
                                        msg (pk 2, (e (b 0 19) 20, sign (sk 2) (ONE, e (b 0 19) 20)));
                                        bol
                                          (eqm (to (x4ttt 1 0)) (V 2)) &
                                          (bacc (pk 3) (b 0 19) (r 20) (pi2 (x4ttt 1 0))); 
                                        msg ok; bol (eqm (to (x54t 1 0)) (V 1));
                                        msg
                                          (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (r 25),
                                           sign (sk 1)
                                                (TWO, enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (r 25)))]). 
       simpl. repeat unfold mixnet, mchecks. 
        rewrite UFCMA with (n:=1) (t:= (TWO, pi1 (pi1 (x76t 0 1)))) (u:= (pi2 (pi1 (x76t 0 1)))); try split; try reflexivity; simpl.

        rewrite UFCMA with (n:=1) (t:= (TWO, pi1 (pi1 (x76t 1 0)))) (u:= (pi2 (pi1 (x76t 1 0)))); try split; try reflexivity; simpl.
        rewrite UFCMA with (n:=2) (t:= (TWO, pi1 (pi2 (x76t 0 1)))) (u:= (pi2 (pi2 (x76t 0 1)))); try split; try reflexivity; simpl.

           rewrite UFCMA with (n:=2) (t:= (TWO, pi1 (pi2 (x76t 1 0)))) (u:= (pi2 (pi2 (x76t 1 0)))); try split; try reflexivity; simpl. 
simpl. 
 
repeat aply_pair_eq; try rewrite eq_true; repeat rewrite andB_TRue_l.
  rewrite eq_sym with (t1:= TWO) (t2:= ONE). simpl.
  try rewrite oTwoneq; try rewrite oThreeneq; try rewrite tThreeneq. simpl.
repeat rewrite andB_FAlse_l. repeat rewrite IFFALSE_B.
  repeat  unfold andB. 
aply_eqbr_ver (pi1 (pi1 (x76t 0 1))). simpl.
aply_eqbr_ver (pi1 (pi1 (x76t 1 0))).
simpl.


  repeat rewrite dep_enc.  repeat rewrite dep_enc with (n:= 5) (z:= (rr (N 25))).
apply IFBRANCH_M1 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
    bol
      (ifb (eqm (to (x2t 0)) (V 1)) (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)))
         FAlse); msg ok; bol (eqm (to (x3tt 0)) (V 2));
    msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)));
    bol
      (ifb (eqm (to (x4ttt 0 1)) (V 2))
         (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1))) FAlse); 
    msg ok; bol (eqm (to (x54t 0 1)) (V 1));
    msg
      (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (r 25),
      sign (sk 1)
        (TWO, enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (r 25)));
    bol (eqm (to (x65t 0 1)) (V 2));
    msg
      (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) (pk 5) (r 37),
      sign (sk 2)
        (TWO,
        enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) (pk 5) (r 37)))]) (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)));
   bol
     (ifb (eqm (to (x2t 1)) (V 1)) (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)))
        FAlse); msg ok; bol (eqm (to (x3tt 1)) (V 2));
   msg (pk 2, (e (b 0 19) 20, sign (sk 2) (ONE, e (b 0 19) 20)));
   bol
     (ifb (eqm (to (x4ttt 1 0)) (V 2))
        (bacc (pk 3) (b 0 19) (r 20) (pi2 (x4ttt 1 0))) FAlse); 
   msg ok; bol (eqm (to (x54t 1 0)) (V 1));
   msg
     (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (r 25),
     sign (sk 1)
       (TWO, enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (r 25)));
   bol (eqm (to (x65t 1 0)) (V 2));
   msg
     (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) (pk 5) (r 37),
     sign (sk 2)
       (TWO,
       enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) (pk 5) (r 37)))]). simpl.
 
(**********************************************************)

Ltac comm_swaptac :=

 pose proof( commit_swap (vt 0) (vt 1) _ 7 7 19 19 [ msg (r 25); msg (r 37); msg (sk 1); msg (sk 2); msg (r 8); msg (r 20); msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1))]) as H; simpl in H;
assert( (L (vt 0)) # (L (vt 1))) as H0; try apply len_f1; try apply len_nonce;
eapply EQmsg' in H0;
apply H in H0; clear H; rename H0 into H; try reflexivity; appconst H;
x1checks x1 x1 H; bterm 0 1 7 H; funapp_vtrm 1 0 1 7 8 ONE H;
x1checks (x2t 0) (x2t 1) H; 
bacctac 0 1 7 8 (x2t 0) (x2t 1) H;
bterm 1 0 19 H;
funapp_vtrm 2 1 0 19 20 ONE H;
funapptrmhyp (bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)))) (bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)))) H;
x1checks (x3tt 0) (x3tt 1) H;
funapp_vtrm 2 1 0 19 20 ONE H;
x1checks (x4ttt 0 1) (x4ttt 1 0) H;
bacctac 1 0 19 20 (x4ttt 0 1) (x4ttt 1 0) H;
funapptrmhyp (bol (eqm (to (x4ttt 0 1)) (V 2)) & (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1)))) (bol (eqm (to (x4ttt 1 0)) (V 2)) & (bacc (pk 3) (b 0 19) (r 20) (pi2 (x4ttt 1 0)))) H;
x1checks (x54t 0 1) (x54t 1 0) H.
 

Ltac votetac c1 c1' n n' n'' x x' H := 


  funapptrmhyp (msg (unblind c1 (pk 3) (r n) x)) (msg (unblind c1' (pk 3) (r n) x')) H; 
funapptrmhyp (msg (enc (unblind c1 (pk 3) (r n) x) (pk 5) (r n'))) (msg (enc (unblind c1' (pk 3) (r n) x') (pk 5) (r n'))) H;
funapptrmhyp (msg (TWO, (enc (unblind c1 (pk 3) (r n) x) (pk 5) (rr (N n'))))) (msg (TWO, (enc (unblind c1' (pk 3) (r n) x') (pk 5) (rr (N n'))))) H;
funapptrmhyp (msg (sign (sk n'') (TWO, (enc (unblind c1 (pk 3) (r n) x) (pk 5) (rr (N n'))))))  (msg (sign (sk n'') (TWO, (enc (unblind c1' (pk 3) (r n) x') (pk 5) (rr (N n')))))) H; 
funapptrmhyp (msg ((enc (unblind c1 (pk 3) (r n) x) (pk 5) (rr (N n'))), (sign (sk n'') (TWO, (enc (unblind c1 (pk 3) (r n) x) (pk 5) (rr (N n')))))))
             (msg ((enc (unblind c1' (pk 3) (r n) x') (pk 5) (rr (N n'))), (sign (sk n'') (TWO, (enc (unblind c1' (pk 3) (r n) x') (pk 5) (rr (N n'))))))) H.

 
(*
  funapptrmhyp (msg (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0)))) (msg (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1)))) H;
funapptrmhyp (msg (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (r 25))) (msg (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (r 25))) H;
funapptrmhyp (msg (TWO, (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (rr (N 25))))) (msg (TWO, (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25))))) H;
funapptrmhyp (msg (sign (sk 1) (TWO, (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (rr (N 25))))))  (msg (sign (sk 1) (TWO, (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25)))))) H; 
funapptrmhyp (msg ((enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (rr (N 25))), (sign (sk 1) (TWO, (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (rr (N 25)))))))  (msg ((enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25))), (sign (sk 1) (TWO, (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25))))))) H.
*)

(*
funapptrmhyp (msg (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1)))) (msg (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0)))) H;
funapptrmhyp (msg (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) (pk 5) (rr (N 37)))) (msg (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) (pk 5) (rr (N 37)))) H;
funapptrmhyp (msg (TWO, (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) (pk 5) (rr (N 37))))) (msg (TWO, (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) (pk 5) (rr (N 37))))) H; funapptrmhyp (msg (sign (sk 2) (TWO, (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) (pk 5) (rr (N 37)))))) (msg (sign (sk 2) (TWO, (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) (pk 5) (rr (N 37)))))) H;  funapptrmhyp (msg ((enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) (pk 5) (rr (N 37))), (sign (sk 2) (TWO, (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) (pk 5) (rr (N 37))))))) (msg ((enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) (pk 5) (rr (N 37))), (sign (sk 2) (TWO, (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) (pk 5) (rr (N 37))))))) H.
*)
Ltac pi12x x x' H:=
  
  x1checks x x' H;
  funapptrmhyp (bol (eqm (to x) (pk 5))) (bol (eqm (to x') (pk 5))) H;
  funapptrmhyp (msg (pi1 x)) (msg (pi1 x')) H;
  funapptrmhyp (msg (pi2 x)) (msg (pi2 x')) H;
  funapptrmhyp (msg (pi1 (pi1 x))) (msg (pi1 (pi1 x'))) H;
  funapptrmhyp (msg (pi1 (pi2 x))) (msg (pi1 (pi2 x'))) H;
  funapptrmhyp (msg (pi2 (pi1 x))) (msg (pi2 (pi1 x'))) H;
  funapptrmhyp (msg (pi2 (pi2 x))) (msg (pi2 (pi2 x'))) H.
 
  (*x1checks (x76t 0 1) (x76t 1 0) H;
  funapptrmhyp (msg (pi1 (x76t 0 1))) (msg (pi1 (x76t 1 0))) H;
  funapptrmhyp (msg (pi2 (x76t 0 1))) (msg (pi2 (x76t 1 0))) H;
  funapptrmhyp (msg (pi1 (pi1 (x76t 0 1)))) (msg (pi1 (pi1 (x76t 1 0)))) H;
  funapptrmhyp (msg (pi1 (pi2 (x76t 0 1)))) (msg (pi1 (pi2 (x76t 1 0)))) H;
  funapptrmhyp (msg (pi2 (pi1 (x76t 0 1)))) (msg (pi2 (pi1 (x76t 1 0)))) H;
  funapptrmhyp (msg (pi2 (pi2 (x76t 0 1)))) (msg (pi2 (pi2 (x76t 1 0)))) H;
   *)

  Ltac mixvertac c c' n x x' n' n''  x1 x1' H := 
   
 funapptrmhyp (bol (eqm (pi1 x) (enc (unblind c (pk 3) (r n) x1) (pk 5) (r n')))) (bol (eqm (pi1 x') (enc (unblind c' (pk 3) (r n) x1') (pk 5) (r n')))) H; 
     
  funapptrmhyp (bol (ver (pk n'') (TWO, enc (unblind c (pk 3) (r n) x1) (pk 5) (r n')) (pi2 x))) (bol (ver (pk n'') (TWO, enc (unblind c' (pk 3) (r n) x1') (pk 5) (r n')) (pi2 x'))) H;
  

    funapptrmhyp (bol (ifb (eqm (pi1 x) (enc (unblind c (pk 3) (r n) x1) (pk 5) (r n'))) (ver (pk n'') (TWO, enc (unblind c (pk 3) (r n) x1) (pk 5) (r n')) (pi2 x)) FAlse))
                 (bol (ifb (eqm (pi1 x') (enc (unblind c' (pk 3) (r n) x1') (pk 5) (r n'))) (ver (pk n'') (TWO, enc (unblind c' (pk 3) (r n) x1') (pk 5) (r n')) (pi2 x')) FAlse)) H.

  
  
   
  Ltac mixvertac' c1 c1' n c2 c2' n' n'' n''' x x' x1 x1' x2 x2' H:=


    funapptrmhyp (bol  (ifb (eqm (to x) (pk 5)) (ifb (eqm (pi1 (pi1 x)) (enc (unblind c1 (pk 3) (r n) (pi1 x1)) (pk 5) (r n''))) (ver (pk 1) (TWO, enc (unblind c1 (pk 3) (r n) (pi1 x1)) (pk 5) (r n'')) (pi2 (pi1 x))) FAlse) FAlse))
                 (bol (ifb (eqm (to x') (pk 5)) (ifb (eqm (pi1 (pi1 x')) (enc (unblind c1' (pk 3) (r n) (pi1 x1')) (pk 5) (r n''))) (ver (pk 1) (TWO, enc (unblind c1' (pk 3) (r n) (pi1 x1')) (pk 5) (r n'')) (pi2 (pi1 x'))) FAlse) FAlse)) H;



      

    funapptrmhyp (bol (ifb (ifb (eqm (to x) (pk 5))
                                (ifb (eqm (pi1 (pi1 x)) (enc (unblind c1 (pk 3) (r n) (pi1 x1)) (pk 5) (r n''))) (ver (pk 1) (TWO, enc (unblind c1 (pk 3) (r n) (pi1 x1)) (pk 5) (r n'')) (pi2 (pi1 x))) FAlse) FAlse)
                           (ifb    (eqm (pi1 (pi2 x)) (enc (unblind c2 (pk 3) (r n') (pi2 x2)) (pk 5) (r n'''))) (ver (pk 2) (TWO, enc (unblind c2 (pk 3) (r n') (pi2 x2)) (pk 5) (r n''')) (pi2 (pi2 x))) FAlse) FAlse))

                 (bol (ifb (ifb (eqm (to x') (pk 5))
                                (ifb (eqm (pi1 (pi1 x')) (enc (unblind c1' (pk 3) (r n) (pi1 x1')) (pk 5) (r n''))) (ver (pk 1) (TWO, enc (unblind c1' (pk 3) (r n) (pi1 x1')) (pk 5) (r n'')) (pi2 (pi1 x'))) FAlse) FAlse)
                           (ifb (eqm (pi1 (pi2 x')) (enc (unblind (b 0 19) (pk 3) (r n') (pi2 x2')) (pk 5) (r n'''))) (ver (pk 2) (TWO, enc (unblind (b 0 19) (pk 3) (r n') (pi2 x2')) (pk 5) (r n''')) (pi2 (pi2 x'))) FAlse) FAlse)) H.
 
(*
    
    
    funapptrmhyp (bol  (ifb (eqm (to (x76t 0 1)) (pk 5)) (ifb (eqm (pi1 (pi1 (x76t 0 1))) (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (r 25))) (ver (pk 1) (TWO, enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (r 25)) (pi2 (pi1 (x76t 0 1)))) FAlse) FAlse))
                 (bol (ifb (eqm (to (x76t 1 0)) (pk 5)) (ifb (eqm (pi1 (pi1 (x76t 1 0))) (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (r 25))) (ver (pk 1) (TWO, enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (r 25)) (pi2 (pi1 (x76t 1 0)))) FAlse) FAlse)) H;



      

    funapptrmhyp (bol (ifb (ifb (eqm (to (x76t 0 1)) (pk 5))
                                (ifb (eqm (pi1 (pi1 (x76t 0 1))) (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (r 25))) (ver (pk 1) (TWO, enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (r 25)) (pi2 (pi1 (x76t 0 1)))) FAlse) FAlse)
                           (ifb    (eqm (pi1 (pi2 (x76t 0 1))) (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) (pk 5) (r 37))) (ver (pk 2) (TWO, enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) (pk 5) (r 37)) (pi2 (pi2 (x76t 0 1)))) FAlse) FAlse))

                 (bol (ifb (ifb (eqm (to (x76t 1 0)) (pk 5))
                                (ifb (eqm (pi1 (pi1 (x76t 1 0))) (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (r 25))) (ver (pk 1) (TWO, enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (r 25)) (pi2 (pi1 (x76t 1 0)))) FAlse) FAlse)
                           (ifb (eqm (pi1 (pi2 (x76t 1 0))) (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) (pk 5) (r 37))) (ver (pk 2) (TWO, enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) (pk 5) (r 37)) (pi2 (pi2 (x76t 1 0)))) FAlse) FAlse)) H. *)
 
 Ltac shuftac c1 c1' n c2 c2' n' x1 x1' x2 x2' H:= 
   funapptrmhyp (msg (shuf (unblind c1 (pk 3) (r n) x1) (unblind c2 (pk 3) (r n') x2))) (msg (shuf (unblind c1' (pk 3) (r n) x1') (unblind c2' (pk 3) (r n') x2'))) H. 
 
 (comm_swaptac; simpl; votetac (b 0 7) (b 1 7) 8 25 1 (pi1 (x2t 0)) (pi1 (x2t 1)) H; x1checks (x65t 0 1) (x65t 1 0) H;
votetac (b 1 19) (b 0 19) 20 37 2 (pi2 (x4ttt 0 1)) (pi2 (x4ttt 1 0)) H;  pi12x (x76t 0 1) (x76t 1 0) H;  mixvertac (b 0 7) (b 1 7) 8 (pi1 (x76t 0 1)) (pi1 (x76t 1 0)) 25 1 (pi1 (x2t 0)) (pi1 (x2t 1)) H;
   
 mixvertac (b 1 19) (b 0 19) 20 (pi2 (x76t 0 1)) (pi2 (x76t 1 0)) 37 2 (pi2 (x4ttt 0 1)) (pi2 (x4ttt 1 0)) H; mixvertac' (b 0 7) (b 1 7) 8 (b 1 19) (b 0 19) 20 25 37 (x76t 0 1) (x76t 1 0) (x2t 0) (x2t 1) (x4ttt 0 1) (x4ttt 1 0) H;
 shuftac (b 0 7) (b 1 7) 8 (b 1 19) (b 0 19) 20 (pi1 (x2t 0)) (pi1 (x2t 1)) (pi2 (x4ttt 0 1)) (pi2 (x4ttt 1 0)) H; restrsublis H). 

  (comm_swaptac; simpl; votetac (b 0 7) (b 1 7) 8 25 1 (pi1 (x2t 0)) (pi1 (x2t 1)) H; x1checks (x65t 0 1) (x65t 1 0) H;
votetac (b 1 19) (b 0 19) 20 37 2 (pi2 (x4ttt 0 1)) (pi2 (x4ttt 1 0)) H;  pi12x (x76t 0 1) (x76t 1 0) H;  mixvertac (b 0 7) (b 1 7) 8 (pi1 (x76t 0 1)) (pi1 (x76t 1 0)) 25 1 (pi1 (x2t 0)) (pi1 (x2t 1)) H;
   
 mixvertac (b 1 19) (b 0 19) 20 (pi2 (x76t 0 1)) (pi2 (x76t 1 0)) 37 2 (pi2 (x4ttt 0 1)) (pi2 (x4ttt 1 0)) H; mixvertac' (b 0 7) (b 1 7) 8 (b 1 19) (b 0 19) 20 25 37 (x76t 0 1) (x76t 1 0) (x2t 0) (x2t 1) (x4ttt 0 1) (x4ttt 1 0) H;
 shuftac (b 0 7) (b 1 7) 8 (b 1 19) (b 0 19) 20 (pi1 (x2t 0)) (pi1 (x2t 1)) (pi2 (x4ttt 0 1)) (pi2 (x4ttt 1 0)) H; restrsublis H). 
  (comm_swaptac; simpl; votetac (b 0 7) (b 1 7) 8 25 1 (pi1 (x2t 0)) (pi1 (x2t 1)) H; x1checks (x65t 0 1) (x65t 1 0) H;
votetac (b 1 19) (b 0 19) 20 37 2 (pi2 (x4ttt 0 1)) (pi2 (x4ttt 1 0)) H;  pi12x (x76t 0 1) (x76t 1 0) H;  mixvertac (b 0 7) (b 1 7) 8 (pi1 (x76t 0 1)) (pi1 (x76t 1 0)) 25 1 (pi1 (x2t 0)) (pi1 (x2t 1)) H;
   
 mixvertac (b 1 19) (b 0 19) 20 (pi2 (x76t 0 1)) (pi2 (x76t 1 0)) 37 2 (pi2 (x4ttt 0 1)) (pi2 (x4ttt 1 0)) H; mixvertac' (b 0 7) (b 1 7) 8 (b 1 19) (b 0 19) 20 25 37 (x76t 0 1) (x76t 1 0) (x2t 0) (x2t 1) (x4ttt 0 1) (x4ttt 1 0) H;
 shuftac (b 0 7) (b 1 7) 8 (b 1 19) (b 0 19) 20 (pi1 (x2t 0)) (pi1 (x2t 1)) (pi2 (x4ttt 0 1)) (pi2 (x4ttt 1 0)) H; restrsublis H). 
 repeat unfold mixnet. simpl. repeat unfold mchecks.
 (** apply uf-cma *)

  simpl. repeat unfold mixnet, mchecks. 
        rewrite UFCMA with (n:=1) (t:= (TWO, pi1 (pi1 (x74tftt 0 1)))) (u:= (pi2 (pi1 (x74tftt 0 1)))); try split; try reflexivity; simpl.

        rewrite UFCMA with (n:=1) (t:= (TWO, pi1 (pi1 (x74tftt 1 0)))) (u:= (pi2 (pi1 (x74tftt 1 0)))); try split; try reflexivity; simpl.
        rewrite UFCMA with (n:=2) (t:= (TWO, pi1 (pi2 (x74tftt 0 1)))) (u:= (pi2 (pi2 (x74tftt 0 1)))); try split; try reflexivity; simpl.

           rewrite UFCMA with (n:=2) (t:= (TWO, pi1 (pi2 (x74tftt 1 0)))) (u:= (pi2 (pi2 (x74tftt 1 0)))); try split; try reflexivity; simpl. 
simpl. 
 
repeat aply_pair_eq; try rewrite eq_true; repeat rewrite andB_TRue_l.
  rewrite eq_sym with (t1:= TWO) (t2:= ONE). simpl.
  try rewrite oTwoneq; try rewrite oThreeneq; try rewrite tThreeneq. simpl.
repeat rewrite andB_FAlse_l. repeat rewrite IFFALSE_B.
  repeat  unfold andB. 
aply_eqbr_ver (pi1 (pi1 (x74tftt 0 1))). simpl.
aply_eqbr_ver (pi1 (pi1 (x74tftt 1 0))).
simpl.


  repeat rewrite dep_enc.  repeat rewrite dep_enc with (n:= 5) (z:= (rr (N 38))).  simpl.
apply IFBRANCH_M3 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
    msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
    bol
      (ifb (eqm (to (x2t 0)) (V 1)) (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)))
         FAlse); msg ok; bol (eqm (to (x3tt 0)) (V 2));
    msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)));
    bol
      (ifb (eqm (to (x4ttt 0 1)) (V 2))
         (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1))) FAlse); 
    msg ok; bol (eqm (to (x54t 0 1)) (V 1))]) (ml2:=  [msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
   msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)));
   bol
     (ifb (eqm (to (x2t 1)) (V 1)) (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)))
        FAlse); msg ok; bol (eqm (to (x3tt 1)) (V 2));
   msg (pk 2, (e (b 0 19) 20, sign (sk 2) (ONE, e (b 0 19) 20)));
   bol
     (ifb (eqm (to (x4ttt 1 0)) (V 2))
        (bacc (pk 3) (b 0 19) (r 20) (pi2 (x4ttt 1 0))) FAlse); 
   msg ok; bol (eqm (to (x54t 1 0)) (V 1))]).
simpl. 
comm_swaptac.
Ltac comm_swaptac :=

 pose proof( commit_swap (vt 0) (vt 1) _ 7 7 19 19 [ msg (r 26); msg (r 38); msg (sk 1); msg (sk 2); msg (r 8); msg (r 20); msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1))]) as H; simpl in H;
assert( (L (vt 0)) # (L (vt 1))) as H0; try apply len_f1; try apply len_nonce;
eapply EQmsg' in H0;
apply H in H0; clear H; rename H0 into H; try reflexivity; appconst H;
x1checks x1 x1 H; bterm 0 1 7 H; funapp_vtrm 1 0 1 7 8 ONE H;
x1checks (x2t 0) (x2t 1) H; 
bacctac 0 1 7 8 (x2t 0) (x2t 1) H;
bterm 1 0 19 H;
funapp_vtrm 2 1 0 19 20 ONE H;
funapptrmhyp (bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)))) (bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)))) H;
x1checks (x3tt 0) (x3tt 1) H;
funapp_vtrm 2 1 0 19 20 ONE H;
x1checks (x4ttt 0 1) (x4ttt 1 0) H;
bacctac 1 0 19 20 (x4ttt 0 1) (x4ttt 1 0) H;
funapptrmhyp (bol (eqm (to (x4ttt 0 1)) (V 2)) & (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1)))) (bol (eqm (to (x4ttt 1 0)) (V 2)) & (bacc (pk 3) (b 0 19) (r 20) (pi2 (x4ttt 1 0)))) H;
x1checks (x54t 0 1) (x54t 1 0) H.

 (comm_swaptac; simpl; votetac (b 0 7) (b 1 7) 8 25 1 (pi1 (x2t 0)) (pi1 (x2t 1)) H; x1checks (x65t 0 1) (x65t 1 0) H;
votetac (b 1 19) (b 0 19) 20 37 2 (pi2 (x4ttt 0 1)) (pi2 (x4ttt 1 0)) H;  pi12x (x76t 0 1) (x76t 1 0) H;  mixvertac (b 0 7) (b 1 7) 8 (pi1 (x76t 0 1)) (pi1 (x76t 1 0)) 25 1 (pi1 (x2t 0)) (pi1 (x2t 1)) H;
   
 mixvertac (b 1 19) (b 0 19) 20 (pi2 (x76t 0 1)) (pi2 (x76t 1 0)) 37 2 (pi2 (x4ttt 0 1)) (pi2 (x4ttt 1 0)) H; mixvertac' H;
 shuftac (b 0 7) (b 1 7) 8 (b 1 19) (b 0 19) 20 (pi1 (x2t 0)) (pi1 (x2t 1)) (pi2 (x4ttt 0 1)) (pi2 (x4ttt 1 0)) H; restrsublis H). simpl.
(***************trace 2*******************************************)
(*****************************************************************)
simpl.
pose proof( commit_swap (vt 0) (vt 1) _ 7 7 19 19 [ msg (r 25); msg (r 37); msg (sk 1); msg (sk 2); msg (r 8); msg (r 20); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1))]); simpl in H.
assert( (L (vt 0)) # (L (vt 1))).
eapply len_f1; eapply len_nonce.
eapply EQmsg' in H0. 
apply H in H0; clear H; rename H0 into H; try reflexivity.
    appconst H.
x1checks x1 x1 H. 
bterm 0 1 7 H.
funapp_vtrm 1 0 1 7 8 ONE H.
x1checks (x2t 0) (x2t 1) H.
bacctac 0 1 7 8 (x2t 0) (x2t 1) H.
bterm 1 0 19 H.
funapp_vtrm 2 1 0 19 20 ONE H.
funapptrmhyp (bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)))) (bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)))) H.
x1checks (x3tt 0) (x3tt 1) H.
funapp_vtrm 2 1 0 19 20 ONE H.
x1checks (x4ttt 0 1) (x4ttt 1 0) H.
bacctac 1 0 19 20 (x4ttt 0 1) (x4ttt 1 0) H.
funapptrmhyp (bol (eqm (to (x4ttt 0 1)) (V 2)) & (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1)))) (bol (eqm (to (x4ttt 1 0)) (V 2)) & (bacc (pk 3) (b 0 19) (r 20) (pi2 (x4ttt 1 0)))) H.
x1checks (x54t 0 1) (x54t 1 0) H.
funapptrmhyp (msg (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0)))) (msg (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1)))) H.
funapptrmhyp (msg (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (r 25))) (msg (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (r 25))) H.
funapptrmhyp (msg (TWO, (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (rr (N 25))))) (msg (TWO, (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25))))) H.
funapptrmhyp (msg (sign (sk 1) (TWO, (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (rr (N 25))))))  (msg (sign (sk 1) (TWO, (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25)))))) H. 
funapptrmhyp (msg ((enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (rr (N 25))), (sign (sk 1) (TWO, (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (rr (N 25)))))))  (msg ((enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25))), (sign (sk 1) (TWO, (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25))))))) H.
x1checks (x65t 0 1) (x65t 1 0) H.
funapptrmhyp (msg (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1)))) (msg (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0)))) H.
funapptrmhyp (msg (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
            (pk 5) (rr (N 37)))) (msg (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
            (pk 5) (rr (N 37)))) H.
funapptrmhyp (msg (TWO, (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
            (pk 5) (rr (N 37))))) (msg (TWO, (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
            (pk 5) (rr (N 37))))) H.   
funapptrmhyp (msg (sign (sk 2) (TWO, (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
            (pk 5) (rr (N 37)))))) (msg (sign (sk 2) (TWO, (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
            (pk 5) (rr (N 37)))))) H.  

funapptrmhyp (msg ((enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
            (pk 5) (rr (N 37))), (sign (sk 2) (TWO, (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
            (pk 5) (rr (N 37))))))) (msg ((enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
            (pk 5) (rr (N 37))), (sign (sk 2) (TWO, (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
            (pk 5) (rr (N 37))))))) H.   
x1checks (x76t 0 1) (x76t 1 0) H.
funapptrmhyp (msg (pi1 (x76t 0 1))) (msg (pi1 (x76t 1 0))) H.
funapptrmhyp (msg (pi2 (x76t 0 1))) (msg (pi2 (x76t 1 0))) H.  
funapptrmhyp (msg (pi1 (pi1 (x76t 0 1)))) (msg (pi1 (pi1 (x76t 1 0)))) H.
funapptrmhyp (msg (pi1 (pi2 (x76t 0 1)))) (msg (pi1 (pi2 (x76t 1 0)))) H.
funapptrmhyp (msg (pi2 (pi1 (x76t 0 1)))) (msg (pi2 (pi1 (x76t 1 0)))) H.
funapptrmhyp (msg (pi2 (pi2 (x76t 0 1)))) (msg (pi2 (pi2 (x76t 1 0)))) H.
funapptrmhyp (bol (ver (pk 1)
                  (TWO,
                  enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                    (pk 5) (r 25)) (pi2 (pi1 (x76t 0 1))))) (bol (ver (pk 1)
                 (TWO,
                 enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
                   (pk 5) (r 25)) (pi2 (pi1 (x76t 1 0))))) H.

funapptrmhyp (bol (ver (pk 2)
               (TWO,
               enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
                 (pk 5) (r 37)) (pi2 (pi2 (x76t 0 1))))) (bol (ver (pk 2)
              (TWO,
              enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
                (pk 5) (r 37)) (pi2 (pi2 (x76t 1 0))))) H.
funapptrmhyp (bol (eqm (pi1 (pi1 (x76t 0 1)))
                  (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                     (pk 5) (r 25)))) (bol (eqm (pi1 (pi1 (x76t 1 0)))
                 (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
                    (pk 5) (r 25)))) H.
funapptrmhyp (bol (eqm (pi1 (pi2 (x76t 0 1)))
               (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
                  (pk 5) (r 37)))) (bol (eqm (pi1 (pi2 (x76t 1 0)))
              (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
                 (pk 5) (r 37)))) H.
funapptrmhyp (bol (ifb
            (eqm (pi1 (pi2 (x76t 0 1)))
               (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
                  (pk 5) (r 37)))
            (ver (pk 2)
               (TWO,
               enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
                 (pk 5) (r 37)) (pi2 (pi2 (x76t 0 1)))) FAlse)) (bol (ifb
           (eqm (pi1 (pi2 (x76t 1 0)))
              (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
                 (pk 5) (r 37)))
           (ver (pk 2)
              (TWO,
              enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
                (pk 5) (r 37)) (pi2 (pi2 (x76t 1 0)))) FAlse)) H.
funapptrmhyp (bol (ifb
               (eqm (pi1 (pi1 (x76t 0 1)))
                  (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                     (pk 5) (r 25)))
               (ver (pk 1)
                  (TWO,
                  enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                    (pk 5) (r 25)) (pi2 (pi1 (x76t 0 1)))) FAlse)) (bol (ifb
              (eqm (pi1 (pi1 (x76t 1 0)))
                 (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
                    (pk 5) (r 25)))
              (ver (pk 1)
                 (TWO,
                 enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
                     (pk 5) (r 25)) (pi2 (pi1 (x76t 1 0)))) FAlse)) H.
funapptrmhyp (bol (eqm (to (x76t 0 1)) (pk 5))) (bol (eqm (to (x76t 1 0)) (pk 5))) H.
funapptrmhyp (bol  (ifb (eqm (to (x76t 0 1)) (pk 5))
            (ifb
               (eqm (pi1 (pi1 (x76t 0 1)))
                  (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                     (pk 5) (r 25)))
               (ver (pk 1)
                  (TWO,
                  enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                    (pk 5) (r 25)) (pi2 (pi1 (x76t 0 1)))) FAlse) FAlse)) (bol (ifb (eqm (to (x76t 1 0)) (pk 5))
           (ifb
              (eqm (pi1 (pi1 (x76t 1 0)))
                 (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
                    (pk 5) (r 25)))
              (ver (pk 1)
                 (TWO,
                 enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
                     (pk 5) (r 25)) (pi2 (pi1 (x76t 1 0)))) FAlse) FAlse)) H. 
funapptrmhyp (msg (pi1 (x2t 0))) (msg (pi1 (x2t 1))) H.
funapptrmhyp (msg (unblind (commit (v (N 0)) (rr (N 7)))
            (pk 3) (rr (N 8)) (pi1 (x2t 0)))) (msg (unblind (commit  (v (N 1)) (rr (N 7)))
           (pk 3) (rr (N 8)) (pi1 (x2t 1)))) H. 
 funapptrmhyp (msg (pi2 (x4ttt 0 1))) (msg (pi2 (x4ttt 1 0))) H.
funapptrmhyp (msg (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1)))) (msg (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0)))) H.
funapptrmhyp (msg (shuf
         (unblind (commit  (v (N 0)) (rr (N 7)))
            (pk 3) (rr (N 8))
            (pi1 (x2t 0)))
         (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1)))))  (msg (shuf
         (unblind (commit  (v (N 1)) (rr (N 7)))
            (pk 3) (rr (N 8))
            (pi1 (x2t 1)))
         (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))))) H.
funapptrmhyp (bol
      (ifb
         (ifb (eqm (to (x76t 0 1)) (pk 5))
            (ifb
               (eqm (pi1 (pi1 (x76t 0 1)))
                  (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                     (pk 5) (r 25)))
               (ver (pk 1)
                  (TWO,
                  enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                    (pk 5) (r 25)) (pi2 (pi1 (x76t 0 1)))) FAlse) FAlse)
         (ifb
            (eqm (pi1 (pi2 (x76t 0 1)))
               (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
                  (pk 5) (r 37)))
            (ver (pk 2)
               (TWO,
               enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
                 (pk 5) (r 37)) (pi2 (pi2 (x76t 0 1)))) FAlse) FAlse)) (bol
     (ifb
        (ifb (eqm (to (x76t 1 0)) (pk 5))
           (ifb
              (eqm (pi1 (pi1 (x76t 1 0)))
                 (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
                    (pk 5) (r 25)))
              (ver (pk 1)
                 (TWO,
                 enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
                   (pk 5) (r 25)) (pi2 (pi1 (x76t 1 0)))) FAlse) FAlse)
        (ifb
           (eqm (pi1 (pi2 (x76t 1 0)))
              (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
                 (pk 5) (r 37)))
           (ver (pk 2)
              (TWO,
              enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
                (pk 5) (r 37)) (pi2 (pi2 (x76t 1 0)))) FAlse) FAlse)) H.
restrsublis H.
(***************trace 2*******************************************)
(*****************************************************************)
simpl.
(** apply ENCCPA *)
(** l ++ [t1] ++ [t2] ~ l ++ [t1] ++ [t2'] *) 
pose proof(ENCCPA' (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0)))  O 0 5 37 37 [  msg (sk 1); msg (sk 2); msg TWO; msg (r 8); msg (r 20); msg (b 0 7); msg (b 1 19); msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
    bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
    msg ok; bol (eqm (to (x3tt 0)) (V 2));
    msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)));
    bol
      (eqm (to (x4ttt 0 1)) (V 2)) &
      (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1))); 
    msg ok; bol (eqm (to (x54t 0 1)) (V 1));
    msg
      (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (r 25))]).
assert( (L (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1)))) # (L (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))))).
try apply len_trm4; try apply len_trm3; try apply len_trm2; try apply len_trm1; try apply len_nonce.
apply EQmsg' in H0. apply H in H0;try reflexivity. clear H. simpl in H0.
rename H0 into H.      


(** l ++ [t1] ++ [t2'] ~ l ++ [t1'] ++ [t2'] *)
pose proof(ENCCPA' (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1)))O 0 5 25 25 [msg (sk 1); msg (sk 2); msg TWO; msg (r 8); msg (r 20); msg (b 0 7); msg (b 1 19); msg (pk 1); msg (pk 2); msg (pk 3); 
      msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
      msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
      bol
        (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
      msg ok; bol (eqm (to (x3tt 0)) (V 2));
      msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)));
      bol
        (eqm (to (x4ttt 0 1)) (V 2)) &
        (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1))); 
      msg ok; bol (eqm (to (x54t 0 1)) (V 1)); 
                  msg
        (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
           (pk 5) (rr (N 37)))]).
     
(**********************************************)
assert( (L (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0)))) # (L (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))))).
    try apply len_trm4; try apply len_trm3; try apply len_trm2; try apply len_trm1; try apply len_nonce.     apply EQmsg' in H1. apply H0 in H1; try reflexivity.
clear H0.
simpl in H1.     
  
 restr_swap_in 23 24 H1. 
assert(tmp1: [msg (sk 1); msg (sk 2); msg TWO; msg (r 8); msg (r 20); msg (b 0 7); msg (b 1 19); 
       msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
       msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
       msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
       bol
         (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
       msg ok; bol (eqm (to (x3tt 0)) (V 2));
       msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)));
       bol
         (eqm (to (x4ttt 0 1)) (V 2)) &
         (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1))); 
       msg ok; bol (eqm (to (x54t 0 1)) (V 1));
       msg (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (r 25));
       msg
         (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
            (pk 5) (rr (N 37)))] ~ [msg (sk 1); msg (sk 2); msg TWO; msg (r 8); msg (r 20); msg (b 0 7); msg (b 1 19); 
       msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
       msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
       msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
       bol
         (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
       msg ok; bol (eqm (to (x3tt 0)) (V 2));
       msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)));
       bol
         (eqm (to (x4ttt 0 1)) (V 2)) &
         (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1))); 
       msg ok; bol (eqm (to (x54t 0 1)) (V 1));
       msg
         (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25)));
       msg
         (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
            (pk 5) (rr (N 37)))]).     
apply EQI_trans with (ml2:= [msg (sk 1); msg (sk 2); msg TWO; msg (r 8); msg (r 20); msg (b 0 7) ;msg (b 1 19); 
      msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
      msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
      msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
      bol
        (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
      msg ok; bol (eqm (to (x3tt 0)) (V 2));
      msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)));
      bol
        (eqm (to (x4ttt 0 1)) (V 2)) &
        (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1))); 
      msg ok; bol (eqm (to (x54t 0 1)) (V 1));
      msg (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (r 25));
      msg
        (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
           (pk 5) (rr (N 37)))]);try assumption.  
clear H H1.
simpl.  
 assert (tmp2:  [msg (sk 1); msg (sk 2); msg TWO; msg (r 8); msg (r 20); msg (b 0 7); msg (b 1 19); 
         msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
         msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
         msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
         bol
           (eqm (to (x2t 0)) (V 1)) &
           (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0))); 
         msg ok; bol (eqm (to (x3tt 0)) (V 2));
         msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)));
         bol
           (eqm (to (x4ttt 0 1)) (V 2)) &
           (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1))); 
         msg ok; bol (eqm (to (x54t 0 1)) (V 1));
         msg
           (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
              (pk 5) (rr (N 25)));
         msg
           (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
              (pk 5) (rr (N 37)))] ~ [msg (sk 1); msg (sk 2); msg TWO; msg (r 8); msg (r 20); msg (b 1 7); msg (b 0 19); msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)));
   bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)));
   msg ok; bol (eqm (to (x3tt 1)) (V 2));
   msg (pk 2, (e (b 0 19) 20, sign (sk 2) (ONE, e (b 0 19) 20)));
   bol
     (eqm (to (x4ttt 1 0)) (V 2)) &
     (bacc (pk 3) (b 0 19) (r 20) (pi2 (x4ttt 1 0))); 
   msg ok; bol (eqm (to (x54t 1 0)) (V 1));
   msg
     (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (r 25)); 
        msg  (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) (pk 5) (r 37))]).
 
pose proof( commit_swap (vt 0) (vt 1) _ 7 7 19 19 [ msg (sk 1); msg (sk 2); msg TWO; msg (r 8);  msg (r 20);  msg (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25)));  msg (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) (pk 5) (rr (N 37)));  msg (pk 1); msg (pk 2); msg (pk 3); 
                                                msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1))]). simpl in H.
assert( (L (vt 0)) # (L (vt 1))). 
eapply len_f1; eapply len_nonce.  
eapply EQmsg' in H0. apply H in H0; clear H; rename H0 into H; try reflexivity. 
funappmconst O H; try reflexivity.
 appconst H.
x1checks x1 x1 H.  
bterm 0 1 7 H.
funapp_vtrm 1 0 1 7 8 ONE H.
x1checks (x2t 0) (x2t 1) H.
bacctac 0 1 7 8 (x2t 0) (x2t 1) H. 
funapptrmhyp (bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)))) (bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)))) H.
x1checks (x3tt 0) (x3tt 1) H.
bterm 1 0 19 H. 
funapp_vtrm 2 1 0 19 20 ONE H.
x1checks (x4ttt 0 1) (x4ttt 1 0) H.
bacctac 1 0 19 20 (x4ttt 0 1) (x4ttt 1 0) H.
funapptrmhyp (bol (eqm (to (x4ttt 0 1)) (V 2)) & (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1)))) (bol (eqm (to (x4ttt 1 0)) (V 2)) & (bacc (pk 3) (b 0 19) (r 20) (pi2 (x4ttt 1 0)))) H.
x1checks (x54t 0 1) (x54t 1 0) H.
restrsublis H.  
assert ( tmp: [msg (sk 1); msg (sk 2); msg TWO; msg (r 8) ; msg (r 20);  msg (b 0 7); msg (b 1 19);
          msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
          msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
          msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
          bol
            (eqm (to (x2t 0)) (V 1)) &
            (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0))); 
          msg ok; bol (eqm (to (x3tt 0)) (V 2));
          msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)));
          bol
            (eqm (to (x4ttt 0 1)) (V 2)) &
            (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1))); 
          msg ok; bol (eqm (to (x54t 0 1)) (V 1));
          msg
            (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (r 25));
          msg
            (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
               (pk 5) (rr (N 37)))] ~ [msg (sk 1); msg (sk 2); msg TWO; msg (r 8); msg (r 20); msg (b 1 7); msg (b 0 19); 
         msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
         msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
         msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)));
         bol
           (eqm (to (x2t 1)) (V 1)) &
           (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1))); 
         msg ok; bol (eqm (to (x3tt 1)) (V 2));
         msg (pk 2, (e (b 0 19) 20, sign (sk 2) (ONE, e (b 0 19) 20)));
         bol
           (eqm (to (x4ttt 1 0)) (V 2)) &
           (bacc (pk 3) (b 0 19) (r 20) (pi2 (x4ttt 1 0))); 
         msg ok; bol (eqm (to (x54t 1 0)) (V 1));
         msg (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (r 25));
         msg
           (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
              (pk 5) (r 37))]). 
apply EQI_trans with (ml2:=  [msg (sk 1); msg (sk 2); msg TWO; msg (r 8); msg (r 20); msg (b 0 7) ; msg (b 1 19); 
         msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
         msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
         msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
         bol
           (eqm (to (x2t 0)) (V 1)) &
           (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0))); 
         msg ok; bol (eqm (to (x3tt 0)) (V 2));
         msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)));
         bol
           (eqm (to (x4ttt 0 1)) (V 2)) &
           (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1))); 
         msg ok; bol (eqm (to (x54t 0 1)) (V 1));
         msg
           (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
              (pk 5) (rr (N 25)));
         msg
           (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
              (pk 5) (rr (N 37)))]). assumption.  assumption. clear tmp1 tmp2.   
appconst tmp. 

funapptrmhyp (msg (TWO, (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                             (pk 5) (rr (N 25))))) (msg (TWO, (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25))))) tmp. 
funapptrmhyp (msg (sign (sk 1) (TWO, (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                                          (pk 5) (rr (N 25)))))) (msg (sign (sk 1) (TWO, (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25)))))) tmp.

funapptrmhyp (msg ((enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
             (pk 5) (rr (N 25))), (sign (sk 1) (TWO, (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
             (pk 5) (rr (N 25))))))) (msg  ((enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25))), (sign (sk 1) (TWO, (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25))))))) tmp.  
x1checks (x65t 0 1) (x65t 1 0) tmp.  simpl.

 
funapptrmhyp (msg (TWO, (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
              (pk 5) (rr (N 37))))) (msg (TWO, (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
                                                    (pk 5) (r 37)))) tmp.

 
funapptrmhyp (msg (sign (sk 2) (TWO, (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
              (pk 5) (rr (N 37)))))) (msg (sign (sk 2) (TWO, (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
                                                                  (pk 5) (r 37))))) tmp.

funapptrmhyp (msg ((enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
              (pk 5) (rr (N 37))), (sign (sk 2) (TWO, (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
              (pk 5) (rr (N 37))))))) (msg ((enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
             (pk 5) (r 37)),(sign (sk 2) (TWO, (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
                                                    (pk 5) (r 37)))))) tmp. 
appconst tmp.    
funapptrmhyp (msg (x76t 0 1)) (msg (x76t 1 0)) tmp. 
funapptrmhyp (msg (pi1 (x76t 0 1))) (msg (pi1 (x76t 1 0))) tmp.
funapptrmhyp (msg (pi2 (x76t 0 1))) (msg (pi2 (x76t 1 0))) tmp.  
funapptrmhyp (msg (pi1 (pi1 (x76t 0 1)))) (msg (pi1 (pi1 (x76t 1 0)))) tmp.
funapptrmhyp (msg (pi1 (pi2 (x76t 0 1)))) (msg (pi1 (pi2 (x76t 1 0)))) tmp.
funapptrmhyp (msg (pi2 (pi1 (x76t 0 1)))) (msg (pi2 (pi1 (x76t 1 0)))) tmp.
funapptrmhyp (msg (pi2 (pi2 (x76t 0 1)))) (msg (pi2 (pi2 (x76t 1 0)))) tmp.
funapptrmhyp (bol (ver (pk 1)
                  (TWO,
                  enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                    (pk 5) (r 25)) (pi2 (pi1 (x76t 0 1))))) (bol (ver (pk 1)
                 (TWO,
                 enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
                   (pk 5) (r 25)) (pi2 (pi1 (x76t 1 0))))) tmp.

funapptrmhyp (bol (ver (pk 2)
               (TWO,
               enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
                 (pk 5) (r 37)) (pi2 (pi2 (x76t 0 1))))) (bol (ver (pk 2)
              (TWO,
              enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
                (pk 5) (r 37)) (pi2 (pi2 (x76t 1 0))))) tmp.
funapptrmhyp (bol (eqm (pi1 (pi1 (x76t 0 1)))
                  (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                     (pk 5) (r 25)))) (bol (eqm (pi1 (pi1 (x76t 1 0)))
                 (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
                    (pk 5) (r 25)))) tmp.
funapptrmhyp (bol (eqm (pi1 (pi2 (x76t 0 1)))
               (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
                  (pk 5) (r 37)))) (bol (eqm (pi1 (pi2 (x76t 1 0)))
              (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
                 (pk 5) (r 37)))) tmp.
funapptrmhyp (bol (ifb
            (eqm (pi1 (pi2 (x76t 0 1)))
               (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
                  (pk 5) (r 37)))
            (ver (pk 2)
               (TWO,
               enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
                 (pk 5) (r 37)) (pi2 (pi2 (x76t 0 1)))) FAlse)) (bol (ifb
           (eqm (pi1 (pi2 (x76t 1 0)))
              (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
                 (pk 5) (r 37)))
           (ver (pk 2)
              (TWO,
              enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
                (pk 5) (r 37)) (pi2 (pi2 (x76t 1 0)))) FAlse)) tmp.
funapptrmhyp (bol (ifb
               (eqm (pi1 (pi1 (x76t 0 1)))
                  (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                     (pk 5) (r 25)))
               (ver (pk 1)
                  (TWO,
                  enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                    (pk 5) (r 25)) (pi2 (pi1 (x76t 0 1)))) FAlse)) (bol (ifb
              (eqm (pi1 (pi1 (x76t 1 0)))
                 (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
                    (pk 5) (r 25)))
              (ver (pk 1)
                 (TWO,
                 enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
                     (pk 5) (r 25)) (pi2 (pi1 (x76t 1 0)))) FAlse)) tmp.
funapptrmhyp (msg (to (x76t 0 1))) (msg (to (x76t 1 0))) tmp.
funapptrmhyp (bol (eqm (to (x76t 0 1)) (pk 5))) (bol (eqm (to (x76t 1 0)) (pk 5))) tmp.
funapptrmhyp (bol  (ifb (eqm (to (x76t 0 1)) (pk 5))
            (ifb
               (eqm (pi1 (pi1 (x76t 0 1)))
                  (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                     (pk 5) (r 25)))
               (ver (pk 1)
                  (TWO,
                  enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                    (pk 5) (r 25)) (pi2 (pi1 (x76t 0 1)))) FAlse) FAlse)) (bol (ifb (eqm (to (x76t 1 0)) (pk 5))
           (ifb
              (eqm (pi1 (pi1 (x76t 1 0)))
                 (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
                    (pk 5) (r 25)))
              (ver (pk 1)
                 (TWO,
                 enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
                     (pk 5) (r 25)) (pi2 (pi1 (x76t 1 0)))) FAlse) FAlse)) tmp.
x1checks (x2t 0) (x2t 1) tmp.
funapptrmhyp (msg (pi1 (x2t 0))) (msg (pi1 (x2t 1))) tmp.
funapptrmhyp (msg (unblind (commit (v (N 0)) (rr (N 7)))
            (pk 3) (rr (N 8)) (pi1 (x2t 0)))) (msg (unblind (commit  (v (N 1)) (rr (N 7)))
           (pk 3) (rr (N 8)) (pi1 (x2t 1)))) tmp. 
 
x1checks (x4ttt 0 1) (x4ttt 1 0) tmp.
funapptrmhyp (msg (pi2 (x4ttt 0 1))) (msg (pi2 (x4ttt 1 0))) tmp.
funapptrmhyp (msg (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1)))) (msg (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0)))) tmp.
funapptrmhyp (msg (shuf
         (unblind (commit  (v (N 0)) (rr (N 7)))
            (pk 3) (rr (N 8))
            (pi1 (x2t 0)))
         (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1)))))  (msg (shuf
         (unblind (commit  (v (N 1)) (rr (N 7)))
            (pk 3) (rr (N 8))
            (pi1 (x2t 1)))
         (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))))) tmp.
funapptrmhyp (bol
      (ifb
         (ifb (eqm (to (x76t 0 1)) (pk 5))
            (ifb
               (eqm (pi1 (pi1 (x76t 0 1)))
                  (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                     (pk 5) (r 25)))
               (ver (pk 1)
                  (TWO,
                  enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                    (pk 5) (r 25)) (pi2 (pi1 (x76t 0 1)))) FAlse) FAlse)
         (ifb
            (eqm (pi1 (pi2 (x76t 0 1)))
               (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
                  (pk 5) (r 37)))
            (ver (pk 2)
               (TWO,
               enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
                 (pk 5) (r 37)) (pi2 (pi2 (x76t 0 1)))) FAlse) FAlse)) (bol
     (ifb
        (ifb (eqm (to (x76t 1 0)) (pk 5))
           (ifb
              (eqm (pi1 (pi1 (x76t 1 0)))
                 (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
                    (pk 5) (r 25)))
              (ver (pk 1)
                 (TWO,
                 enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
                   (pk 5) (r 25)) (pi2 (pi1 (x76t 1 0)))) FAlse) FAlse)
        (ifb
           (eqm (pi1 (pi2 (x76t 1 0)))
              (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
                 (pk 5) (r 37)))
           (ver (pk 2)
              (TWO,
              enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
                (pk 5) (r 37)) (pi2 (pi2 (x76t 1 0)))) FAlse) FAlse)) tmp.
restrsublis tmp.





(** apply ENCCPA *)
(** l ++ [t1] ++ [t2] ~ l ++ [t1] ++ [t2'] *) 
pose proof(ENCCPA' (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0)))  O 0 5 37 37 [  msg (sk 1); msg (sk 2); msg TWO; msg (r 8); msg (r 20); msg (b 0 7); msg (b 1 19); msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
    bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
    msg ok; bol (eqm (to (x3tt 0)) (V 2));
    msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)));
    bol
      (eqm (to (x4ttt 0 1)) (V 2)) &
      (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1))); 
    msg ok; bol (eqm (to (x54t 0 1)) (V 1));
    msg
      (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (r 25))]).
assert( (L (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1)))) # (L (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))))).
try apply len_trm4; try apply len_trm3; try apply len_trm2; try apply len_trm1; try apply len_nonce.
apply EQmsg' in H0. apply H in H0;try reflexivity. clear H. simpl in H0.
rename H0 into H.      


(** l ++ [t1] ++ [t2'] ~ l ++ [t1'] ++ [t2'] *)
pose proof(ENCCPA' (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1)))O 0 5 25 25 [msg (sk 1); msg (sk 2); msg TWO; msg (r 8); msg (r 20); msg (b 0 7); msg (b 1 19); msg (pk 1); msg (pk 2); msg (pk 3); 
      msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
      msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
      bol
        (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
      msg ok; bol (eqm (to (x3tt 0)) (V 2));
      msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)));
      bol
        (eqm (to (x4ttt 0 1)) (V 2)) &
        (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1))); 
      msg ok; bol (eqm (to (x54t 0 1)) (V 1)); 
                  msg
        (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
           (pk 5) (rr (N 37)))]).
     
(**********************************************)
assert( (L (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0)))) # (L (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))))).
    try apply len_trm4; try apply len_trm3; try apply len_trm2; try apply len_trm1; try apply len_nonce.     apply EQmsg' in H1. apply H0 in H1; try reflexivity.
clear H0.
simpl in H1.     
  
 restr_swap_in 23 24 H1. 
assert(tmp1: [msg (sk 1); msg (sk 2); msg TWO; msg (r 8); msg (r 20); msg (b 0 7); msg (b 1 19); 
       msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
       msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
       msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
       bol
         (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
       msg ok; bol (eqm (to (x3tt 0)) (V 2));
       msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)));
       bol
         (eqm (to (x4ttt 0 1)) (V 2)) &
         (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1))); 
       msg ok; bol (eqm (to (x54t 0 1)) (V 1));
       msg (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (r 25));
       msg
         (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
            (pk 5) (rr (N 37)))] ~ [msg (sk 1); msg (sk 2); msg TWO; msg (r 8); msg (r 20); msg (b 0 7); msg (b 1 19); 
       msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
       msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
       msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
       bol
         (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
       msg ok; bol (eqm (to (x3tt 0)) (V 2));
       msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)));
       bol
         (eqm (to (x4ttt 0 1)) (V 2)) &
         (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1))); 
       msg ok; bol (eqm (to (x54t 0 1)) (V 1));
       msg
         (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25)));
       msg
         (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
            (pk 5) (rr (N 37)))]).     
apply EQI_trans with (ml2:= [msg (sk 1); msg (sk 2); msg TWO; msg (r 8); msg (r 20); msg (b 0 7) ;msg (b 1 19); 
      msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
      msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
      msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
      bol
        (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
      msg ok; bol (eqm (to (x3tt 0)) (V 2));
      msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)));
      bol
        (eqm (to (x4ttt 0 1)) (V 2)) &
        (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1))); 
      msg ok; bol (eqm (to (x54t 0 1)) (V 1));
      msg (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (r 25));
      msg
        (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
           (pk 5) (rr (N 37)))]);try assumption.  
clear H H1.
simpl.  
 assert (tmp2:  [msg (sk 1); msg (sk 2); msg TWO; msg (r 8); msg (r 20); msg (b 0 7); msg (b 1 19); 
         msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
         msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
         msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
         bol
           (eqm (to (x2t 0)) (V 1)) &
           (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0))); 
         msg ok; bol (eqm (to (x3tt 0)) (V 2));
         msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)));
         bol
           (eqm (to (x4ttt 0 1)) (V 2)) &
           (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1))); 
         msg ok; bol (eqm (to (x54t 0 1)) (V 1));
         msg
           (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
              (pk 5) (rr (N 25)));
         msg
           (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
              (pk 5) (rr (N 37)))] ~ [msg (sk 1); msg (sk 2); msg TWO; msg (r 8); msg (r 20); msg (b 1 7); msg (b 0 19); msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)));
   bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)));
   msg ok; bol (eqm (to (x3tt 1)) (V 2));
   msg (pk 2, (e (b 0 19) 20, sign (sk 2) (ONE, e (b 0 19) 20)));
   bol
     (eqm (to (x4ttt 1 0)) (V 2)) &
     (bacc (pk 3) (b 0 19) (r 20) (pi2 (x4ttt 1 0))); 
   msg ok; bol (eqm (to (x54t 1 0)) (V 1));
   msg
     (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (r 25)); 
        msg  (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) (pk 5) (r 37))]).
 
pose proof( commit_swap (vt 0) (vt 1) _ 7 7 19 19 [ msg (sk 1); msg (sk 2); msg TWO; msg (r 8);  msg (r 20);  msg (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25)));  msg (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) (pk 5) (rr (N 37)));  msg (pk 1); msg (pk 2); msg (pk 3); 
                                                msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1))]). simpl in H.
assert( (L (vt 0)) # (L (vt 1))). 
eapply len_f1; eapply len_nonce.  
eapply EQmsg' in H0. apply H in H0; clear H; rename H0 into H; try reflexivity. 
funappmconst O H; try reflexivity.
 appconst H.
x1checks x1 x1 H.  
bterm 0 1 7 H.
funapp_vtrm 1 0 1 7 8 ONE H.
x1checks (x2t 0) (x2t 1) H.
bacctac 0 1 7 8 (x2t 0) (x2t 1) H. 
funapptrmhyp (bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)))) (bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)))) H.
x1checks (x3tt 0) (x3tt 1) H.
bterm 1 0 19 H. 
funapp_vtrm 2 1 0 19 20 ONE H.
x1checks (x4ttt 0 1) (x4ttt 1 0) H.
bacctac 1 0 19 20 (x4ttt 0 1) (x4ttt 1 0) H.
funapptrmhyp (bol (eqm (to (x4ttt 0 1)) (V 2)) & (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1)))) (bol (eqm (to (x4ttt 1 0)) (V 2)) & (bacc (pk 3) (b 0 19) (r 20) (pi2 (x4ttt 1 0)))) H.
x1checks (x54t 0 1) (x54t 1 0) H.
restrsublis H.  
assert ( tmp: [msg (sk 1); msg (sk 2); msg TWO; msg (r 8) ; msg (r 20);  msg (b 0 7); msg (b 1 19);
          msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
          msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
          msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
          bol
            (eqm (to (x2t 0)) (V 1)) &
            (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0))); 
          msg ok; bol (eqm (to (x3tt 0)) (V 2));
          msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)));
          bol
            (eqm (to (x4ttt 0 1)) (V 2)) &
            (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1))); 
          msg ok; bol (eqm (to (x54t 0 1)) (V 1));
          msg
            (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (r 25));
          msg
            (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
               (pk 5) (rr (N 37)))] ~ [msg (sk 1); msg (sk 2); msg TWO; msg (r 8); msg (r 20); msg (b 1 7); msg (b 0 19); 
         msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
         msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
         msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)));
         bol
           (eqm (to (x2t 1)) (V 1)) &
           (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1))); 
         msg ok; bol (eqm (to (x3tt 1)) (V 2));
         msg (pk 2, (e (b 0 19) 20, sign (sk 2) (ONE, e (b 0 19) 20)));
         bol
           (eqm (to (x4ttt 1 0)) (V 2)) &
           (bacc (pk 3) (b 0 19) (r 20) (pi2 (x4ttt 1 0))); 
         msg ok; bol (eqm (to (x54t 1 0)) (V 1));
         msg (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (r 25));
         msg
           (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
              (pk 5) (r 37))]). 
apply EQI_trans with (ml2:=  [msg (sk 1); msg (sk 2); msg TWO; msg (r 8); msg (r 20); msg (b 0 7) ; msg (b 1 19); 
         msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
         msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
         msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
         bol
           (eqm (to (x2t 0)) (V 1)) &
           (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0))); 
         msg ok; bol (eqm (to (x3tt 0)) (V 2));
         msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)));
         bol
           (eqm (to (x4ttt 0 1)) (V 2)) &
           (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1))); 
         msg ok; bol (eqm (to (x54t 0 1)) (V 1));
         msg
           (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
              (pk 5) (rr (N 25)));
         msg
           (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
              (pk 5) (rr (N 37)))]). assumption.  assumption. clear tmp1 tmp2.   
appconst tmp. 

funapptrmhyp (msg (TWO, (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                             (pk 5) (rr (N 25))))) (msg (TWO, (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25))))) tmp. 
funapptrmhyp (msg (sign (sk 1) (TWO, (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                                          (pk 5) (rr (N 25)))))) (msg (sign (sk 1) (TWO, (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25)))))) tmp.

funapptrmhyp (msg ((enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
             (pk 5) (rr (N 25))), (sign (sk 1) (TWO, (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
             (pk 5) (rr (N 25))))))) (msg  ((enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25))), (sign (sk 1) (TWO, (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25))))))) tmp.  
x1checks (x65t 0 1) (x65t 1 0) tmp.  simpl.

 
funapptrmhyp (msg (TWO, (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
              (pk 5) (rr (N 37))))) (msg (TWO, (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
                                                    (pk 5) (r 37)))) tmp.

 
funapptrmhyp (msg (sign (sk 2) (TWO, (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
              (pk 5) (rr (N 37)))))) (msg (sign (sk 2) (TWO, (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
                                                                  (pk 5) (r 37))))) tmp.

funapptrmhyp (msg ((enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
              (pk 5) (rr (N 37))), (sign (sk 2) (TWO, (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
              (pk 5) (rr (N 37))))))) (msg ((enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
             (pk 5) (r 37)),(sign (sk 2) (TWO, (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
                                                    (pk 5) (r 37)))))) tmp. 
appconst tmp.    
funapptrmhyp (msg (x76t 0 1)) (msg (x76t 1 0)) tmp. 
funapptrmhyp (msg (pi1 (x76t 0 1))) (msg (pi1 (x76t 1 0))) tmp.
funapptrmhyp (msg (pi2 (x76t 0 1))) (msg (pi2 (x76t 1 0))) tmp.  
funapptrmhyp (msg (pi1 (pi1 (x76t 0 1)))) (msg (pi1 (pi1 (x76t 1 0)))) tmp.
funapptrmhyp (msg (pi1 (pi2 (x76t 0 1)))) (msg (pi1 (pi2 (x76t 1 0)))) tmp.
funapptrmhyp (msg (pi2 (pi1 (x76t 0 1)))) (msg (pi2 (pi1 (x76t 1 0)))) tmp.
funapptrmhyp (msg (pi2 (pi2 (x76t 0 1)))) (msg (pi2 (pi2 (x76t 1 0)))) tmp.
funapptrmhyp (bol (ver (pk 1)
                  (TWO,
                  enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                    (pk 5) (r 25)) (pi2 (pi1 (x76t 0 1))))) (bol (ver (pk 1)
                 (TWO,
                 enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
                   (pk 5) (r 25)) (pi2 (pi1 (x76t 1 0))))) tmp.

funapptrmhyp (bol (ver (pk 2)
               (TWO,
               enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
                 (pk 5) (r 37)) (pi2 (pi2 (x76t 0 1))))) (bol (ver (pk 2)
              (TWO,
              enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
                (pk 5) (r 37)) (pi2 (pi2 (x76t 1 0))))) tmp.
funapptrmhyp (bol (eqm (pi1 (pi1 (x76t 0 1)))
                  (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                     (pk 5) (r 25)))) (bol (eqm (pi1 (pi1 (x76t 1 0)))
                 (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
                    (pk 5) (r 25)))) tmp.
funapptrmhyp (bol (eqm (pi1 (pi2 (x76t 0 1)))
               (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
                  (pk 5) (r 37)))) (bol (eqm (pi1 (pi2 (x76t 1 0)))
              (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
                 (pk 5) (r 37)))) tmp.
funapptrmhyp (bol (ifb
            (eqm (pi1 (pi2 (x76t 0 1)))
               (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
                  (pk 5) (r 37)))
            (ver (pk 2)
               (TWO,
               enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
                 (pk 5) (r 37)) (pi2 (pi2 (x76t 0 1)))) FAlse)) (bol (ifb
           (eqm (pi1 (pi2 (x76t 1 0)))
              (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
                 (pk 5) (r 37)))
           (ver (pk 2)
              (TWO,
              enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
                (pk 5) (r 37)) (pi2 (pi2 (x76t 1 0)))) FAlse)) tmp.
funapptrmhyp (bol (ifb
               (eqm (pi1 (pi1 (x76t 0 1)))
                  (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                     (pk 5) (r 25)))
               (ver (pk 1)
                  (TWO,
                  enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                    (pk 5) (r 25)) (pi2 (pi1 (x76t 0 1)))) FAlse)) (bol (ifb
              (eqm (pi1 (pi1 (x76t 1 0)))
                 (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
                    (pk 5) (r 25)))
              (ver (pk 1)
                 (TWO,
                 enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
                     (pk 5) (r 25)) (pi2 (pi1 (x76t 1 0)))) FAlse)) tmp.
funapptrmhyp (msg (to (x76t 0 1))) (msg (to (x76t 1 0))) tmp.
funapptrmhyp (bol (eqm (to (x76t 0 1)) (pk 5))) (bol (eqm (to (x76t 1 0)) (pk 5))) tmp.
funapptrmhyp (bol  (ifb (eqm (to (x76t 0 1)) (pk 5))
            (ifb
               (eqm (pi1 (pi1 (x76t 0 1)))
                  (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                     (pk 5) (r 25)))
               (ver (pk 1)
                  (TWO,
                  enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                    (pk 5) (r 25)) (pi2 (pi1 (x76t 0 1)))) FAlse) FAlse)) (bol (ifb (eqm (to (x76t 1 0)) (pk 5))
           (ifb
              (eqm (pi1 (pi1 (x76t 1 0)))
                 (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
                    (pk 5) (r 25)))
              (ver (pk 1)
                 (TWO,
                 enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
                     (pk 5) (r 25)) (pi2 (pi1 (x76t 1 0)))) FAlse) FAlse)) tmp.
x1checks (x2t 0) (x2t 1) tmp.
funapptrmhyp (msg (pi1 (x2t 0))) (msg (pi1 (x2t 1))) tmp.
funapptrmhyp (msg (unblind (commit (v (N 0)) (rr (N 7)))
            (pk 3) (rr (N 8)) (pi1 (x2t 0)))) (msg (unblind (commit  (v (N 1)) (rr (N 7)))
           (pk 3) (rr (N 8)) (pi1 (x2t 1)))) tmp. 
 
x1checks (x4ttt 0 1) (x4ttt 1 0) tmp.
funapptrmhyp (msg (pi2 (x4ttt 0 1))) (msg (pi2 (x4ttt 1 0))) tmp.
funapptrmhyp (msg (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1)))) (msg (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0)))) tmp.
funapptrmhyp (msg (shuf
         (unblind (commit  (v (N 0)) (rr (N 7)))
            (pk 3) (rr (N 8))
            (pi1 (x2t 0)))
         (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1)))))  (msg (shuf
         (unblind (commit  (v (N 1)) (rr (N 7)))
            (pk 3) (rr (N 8))
            (pi1 (x2t 1)))
         (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))))) tmp.
funapptrmhyp (bol
      (ifb
         (ifb (eqm (to (x76t 0 1)) (pk 5))
            (ifb
               (eqm (pi1 (pi1 (x76t 0 1)))
                  (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                     (pk 5) (r 25)))
               (ver (pk 1)
                  (TWO,
                  enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                    (pk 5) (r 25)) (pi2 (pi1 (x76t 0 1)))) FAlse) FAlse)
         (ifb
            (eqm (pi1 (pi2 (x76t 0 1)))
               (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
                  (pk 5) (r 37)))
            (ver (pk 2)
               (TWO,
               enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
                 (pk 5) (r 37)) (pi2 (pi2 (x76t 0 1)))) FAlse) FAlse)) (bol
     (ifb
        (ifb (eqm (to (x76t 1 0)) (pk 5))
           (ifb
              (eqm (pi1 (pi1 (x76t 1 0)))
                 (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
                    (pk 5) (r 25)))
              (ver (pk 1)
                 (TWO,
                 enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
                   (pk 5) (r 25)) (pi2 (pi1 (x76t 1 0)))) FAlse) FAlse)
        (ifb
           (eqm (pi1 (pi2 (x76t 1 0)))
              (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
                 (pk 5) (r 37)))
           (ver (pk 2)
              (TWO,
              enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
                (pk 5) (r 37)) (pi2 (pi2 (x76t 1 0)))) FAlse) FAlse)) tmp.
restrsublis tmp. simpl. simpl. simpl.
(*************************************************************************************************)
(*************************************************************************************************)
