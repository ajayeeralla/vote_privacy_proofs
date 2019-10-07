 Load "phase22".
 Theorem frame6ind: (phi6 0 1) ~ (phi6 1 0).
Proof.      
repeat unfold phi6, phi5, phi4, phi2, phi1, phi0. simpl.
repeat unfold q0, t1, t2, t3, t4, t5. simpl.
repeat unfold q1, q2, q1_s, q2_s, q1_ss, q2_ss, q1_ss', q2_ss', q1_ss'', q2_ss''.
simpl. 
apply IFBRANCH_M6 with (ml1:= phi0) (ml2:= phi0).
simpl. 
apply IFBRANCH_M5 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)))]) (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)))]). simpl.
repeat unfold q11, q11_s, q11_s', q11_s''.
repeat unfold q111, qs111, qs'111.
apply IFBRANCH_M4 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
    bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
    msg ok]) (ml2:=  [msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)));
   bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)));
   msg ok]).
simpl.

apply IFBRANCH_M3 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
    bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
    msg ok; bol (eqm (to (x3tt 0)) (V 2));
    msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)))])(ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)));
   bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)));
   msg ok; bol (eqm (to (x3tt 1)) (V 2));
   msg (pk 2, (e (b 0 19) 20, sign (sk 2) (ONE, e (b 0 19) 20)))]). simpl. repeat unfold q111v1, q111v2.
apply IFBRANCH_M2 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
    bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
    msg ok; bol (eqm (to (x3tt 0)) (V 2));
    msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)));
    bol
      (eqm (to (x4ttt 0 1)) (V 2)) &
      (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1))); 
    msg ok])(ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)));
   bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)));
   msg ok; bol (eqm (to (x3tt 1)) (V 2));
   msg (pk 2, (e (b 0 19) 20, sign (sk 2) (ONE, e (b 0 19) 20)));
   bol
     (eqm (to (x4ttt 1 0)) (V 2)) &
     (bacc (pk 3) (b 0 19) (r 20) (pi2 (x4ttt 1 0))); 
   msg ok]). simpl. repeat unfold vtrm. repeat unfold voter2.

apply IFBRANCH_M1 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
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
      (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (r 25),
      sign (sk 1)
        (TWO, enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (r 25)))]) (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); 
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
     (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (r 25),
     sign (sk 1)
          (TWO, enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (r 25)))]) . simpl. unfold vtrm.
 

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
restrsublis H.
(*
(** apply ENCCPA *)
(** l ++ [t1] ++ [t2] ~ l ++ [t1] ++ [t2'] *)
pose proof(ENCCPA' (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0)))  O 0 5 37 37 [msg (pk 1); msg (pk 2); msg (pk 3); 
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
      (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (r 25),
      sign (sk 1)
        (TWO, enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (r 25)));
    msg TWO; msg (sk 2); msg (sk 1)]).
assert( (L (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1)))) # (L (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))))).
try apply len_trm4; try apply len_trm3; try apply len_trm2; try apply len_trm1; try apply len_nonce.
apply EQmsg' in H0. apply H in H0;try reflexivity. clear H. simpl in H0.
rename H0 into H.      
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
do 6 (restrproj_in 17 H). 
pose proof(ENCCPA' (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1)))O 0 5 25 25 [msg (sk 1); msg (sk 2); msg TWO; msg (pk 1); msg (pk 2); msg (pk 3); 
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
           (pk 5) (rr (N 37)),
        sign (sk 2)
          (TWO,
          enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
              (pk 5) (rr (N 37))))]).
(**********************************************)
assert( (L (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0)))) # (L (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))))).
    try apply len_trm4; try apply len_trm3; try apply len_trm2; try apply len_trm1; try apply len_nonce.     apply EQmsg' in H1. apply H0 in H1; try reflexivity.
clear H0.
simpl in H1.  
funapptrmhyp (msg (TWO, (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                             (pk 5) (rr (N 25))))) (msg (TWO, (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25))))) H1. 
funapptrmhyp (msg (sign (sk 1) (TWO, (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
                                          (pk 5) (rr (N 25)))))) (msg (sign (sk 1) (TWO, (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25)))))) H1.

funapptrmhyp (msg ((enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
             (pk 5) (rr (N 25))), (sign (sk 1) (TWO, (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) 
             (pk 5) (rr (N 25))))))) (msg  ((enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25))), (sign (sk 1) (TWO, (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25))))))) H1. 
do 3 dropone_in H1. 
do 3 (restrproj_in 17 H1).  
restr_swap_in 16 17 H1.

 
assert(tmp1: [msg (pk 1); msg (pk 2); msg (pk 3); 
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
         (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (r 25),
         sign (sk 1)
           (TWO,
           enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (r 25)));
             msg
         (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
            (pk 5) (rr (N 37)),
         sign (sk 2)
           (TWO,
           enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
             (pk 5) (rr (N 37))))] ~ [msg (pk 1); msg (pk 2); msg (pk 3); 
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
         (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25)),
         sign (sk 1)
           (TWO,
           enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
             (pk 5) (rr (N 25)))); 
       msg
         (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
            (pk 5) (rr (N 37)),
         sign (sk 2)
           (TWO,
           enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
             (pk 5) (rr (N 37))))]). 
apply EQI_trans with (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); 
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
        (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (r 25),
        sign (sk 1)
          (TWO,
          enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (r 25)));
           msg
        (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
           (pk 5) (rr (N 37)),
        sign (sk 2)
          (TWO,
          enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
              (pk 5) (rr (N 37))))]); try assumption. 
clear H H1.
simpl. 
 assert (tmp2: [msg (pk 1); msg (pk 2); msg (pk 3); 
         msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
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
              (pk 5) (rr (N 25)),
           sign (sk 1)
             (TWO,
             enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
               (pk 5) (rr (N 25))));
         msg
           (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
              (pk 5) (rr (N 37)),
           sign (sk 2)
             (TWO,
             enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
               (pk 5) (rr (N 37))))] ~ [msg (pk 1); msg (pk 2); msg (pk 3); 
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
     (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (r 25),
     sign (sk 1)
       (TWO, enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (r 25)));
    msg
     (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) (pk 5) (r 37),
     sign (sk 2)
       (TWO,
       enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) (pk 5) (r 37)))]).
Eval compute in (b 1 7). 
 Eval compute in Fresh [7] [msg (commit (v (N 1)) (rr (N 7)))].
pose proof( commit_swap (vt 0) (vt 1)  _  7 7 19 19 [ msg (sk 1); msg (sk 2); msg (r 8);  msg (r 20); msg
           (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
              (pk 5) (rr (N 25)),
           sign (sk 1)
             (TWO,
             enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
               (pk 5) (rr (N 25))));
         msg
           (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
              (pk 5) (rr (N 37)),
           sign (sk 2)
             (TWO,
             enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
               (pk 5) (rr (N 37)))); msg (pk 1); msg (pk 2); msg (pk 3); 
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
funapptrmhyp (bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)))) (bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)))) H.
x1checks (x3tt 0) (x3tt 1) H.
bterm 1 0 19 H. 
funapp_vtrm 2 1 0 19 20 ONE H.
x1checks (x4ttt 0 1) (x4ttt 1 0) H.
bacctac 1 0 19 20 (x4ttt 0 1) (x4ttt 1 0) H.
funapptrmhyp (bol (eqm (to (x4ttt 0 1)) (V 2)) & (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1)))) (bol (eqm (to (x4ttt 1 0)) (V 2)) & (bacc (pk 3) (b 0 19) (r 20) (pi2 (x4ttt 1 0)))) H.
x1checks (x54t 0 1) (x54t 1 0) H.
restrsublis H. 
assert ( tmp: [msg (pk 1); msg (pk 2); msg (pk 3); 
          msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
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
            (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (r 25),
            sign (sk 1)
              (TWO,
              enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (r 25)));
          msg
            (enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
               (pk 5) (rr (N 37)),
            sign (sk 2)
              (TWO,
              enc (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1))) 
                (pk 5) (rr (N 37))))] ~ [msg (pk 1); msg (pk 2); msg (pk 3); 
         msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
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
         msg
           (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (r 25),
           sign (sk 1)
             (TWO,
             enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (r 25)));
         msg
           (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
              (pk 5) (r 37),
           sign (sk 2)
             (TWO,
             enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
                 (pk 5) (r 37)))]).
apply EQI_trans with (ml2:=  [msg (pk 1); msg (pk 2); msg (pk 3); 
         msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
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
              (pk 5) (rr (N 25)),
           sign (sk 1)
             (TWO,
             enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
               (pk 5) (rr (N 25))));
         msg
           (enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
              (pk 5) (rr (N 37)),
           sign (sk 2)
             (TWO,
             enc (unblind (b 0 19) (pk 3) (r 20) (pi2 (x4ttt 1 0))) 
                 (pk 5) (rr (N 37))))]); try assumption. simpl.  clear tmp1 tmp2.  
appconst tmp.
x1checks (x65t 0 1) (x65t 1 0) tmp.
restrsublis tmp. simpl.
*)