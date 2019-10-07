  Load "phase21".
Theorem frame5ind: (phi5 0 1) ~ (phi5 1 0). 
Proof.      
repeat unfold       phi5, phi4, phi2, phi1, phi0. simpl.
repeat unfold q0, t1, t2, t3, t4. simpl.
repeat unfold q1, q2, q1_s, q2_s, q1_ss, q2_ss, q1_ss', q2_ss'.
simpl.  
apply IFBRANCH_M5 with (ml1:= phi0) (ml2:= phi0).
simpl. 
apply IFBRANCH_M4 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)))]) (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)))]). simpl.
repeat unfold q11, q11_s, q11_s'.        
repeat unfold q111, qs111. 
apply IFBRANCH_M3 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
    bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
    msg ok]) (ml2:=  [msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)));
   bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)));
   msg ok]).
simpl.

apply IFBRANCH_M2 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
    bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
    msg ok; bol (eqm (to (x3tt 0)) (V 2));
    msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)))])(ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)));
   bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)));
   msg ok; bol (eqm (to (x3tt 1)) (V 2));
   msg (pk 2, (e (b 0 19) 20, sign (sk 2) (ONE, e (b 0 19) 20)))]). simpl. repeat unfold q111v1. 
apply IFBRANCH_M1 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); 
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
   msg ok]). simpl. repeat unfold vtrm. 

pose proof( commit_swap (vt 0) (vt 1) _ 7 7 19 19 [ msg (r 25); msg (sk 1); msg (sk 2); msg (r 8); msg (r 20); msg (pk 1); msg (pk 2); msg (pk 3); 
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
restrsublis H.
(*(** apply ENCCPA *)

assert(lenc: (L (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0)))) #  (L (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))))).
         
try apply len_trm4; try apply len_trm3; try apply len_trm2; try apply len_trm1; try apply len_nonce.
       
    
pose proof(ENCCPA' (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1)))  O 0 5 25 25 [msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
    bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
    msg ok; bol (eqm (to (x3tt 0)) (V 2));
    msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)));
    bol
      (eqm (to (x4ttt 0 1)) (V 2)) &
      (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1))); 
    msg ok; bol (eqm (to (x54t 0 1)) (V 1)); msg (sk 1); msg TWO]).
apply EQmsg' in lenc.
apply H in lenc; try reflexivity.
clear H; rename lenc into H.  simpl.     simpl in H.

funapptrmhyp (msg (TWO, (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (rr (N 25))))) (msg (TWO, (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25))))) H.
 
funapptrmhyp (msg (sign (sk 1) (TWO, (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (rr (N 25))))))  (msg (sign (sk 1) (TWO, (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25)))))) H.
funapptrmhyp (msg ((enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (rr (N 25))), (sign (sk 1) (TWO, (enc (unblind (b 0 7) (pk 3) (r 8) (pi1 (x2t 0))) (pk 5) (rr (N 25)))))))  (msg ((enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25))), (sign (sk 1) (TWO, (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25))))))) H.  
do 5 (restrproj_in 16 H). rename H into H'.

assert([msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
    bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
    msg ok; bol (eqm (to (x3tt 0)) (V 2));
    msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)));
    bol
      (eqm (to (x4ttt 0 1)) (V 2)) &
      (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1))); 
    msg ok; bol (eqm (to (x54t 0 1)) (V 1)); msg
     (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (r 25),
     sign (sk 1)
       (TWO, enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (r 25)))] ~ [msg (pk 1); msg (pk 2); msg (pk 3); 
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
       (TWO, enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (r 25)))]). 
pose proof( commit_swap (vt 0) (vt 1) _ 7 7 19 19 [ msg (sk 1); msg (sk 2); msg (r 8); msg (r 20); msg (enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) (pk 5) (rr (N 25)),
         sign (sk 1)
           (TWO,
           enc (unblind (b 1 7) (pk 3) (r 8) (pi1 (x2t 1))) 
             (pk 5) (rr (N 25)))); msg (pk 1); msg (pk 2); msg (pk 3); 
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
x1checks (x54t 0 1) (x54t 1 0) H.   unfold r. 
restrsublis H.  simpl.
*)
