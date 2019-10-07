Load "phase33".

Theorem frame10ind: (phi10 0 1) ~ (phi10 1 0).
Proof. repeat unfold phi10, phi9, phi8, phi7, phi6, phi5, phi4, phi3, phi2, phi1.
       simpl. repeat unfold t9, t8, t7, t6, t5, t4, t3, t2, t1.
       repeat unfold q1, q2, q1_s, q2_s, q1_ss, q2_ss, q1_ss', q2_ss', q1_ss'', q2_ss'', q1_ss''', q2_ss'''.
       apply IFBRANCH_M10 with (ml1:= phi0) (ml2:= phi0). simpl.
       apply IFBRANCH_M9 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
                                      msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
                                      msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)))])
                                (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
                                        msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
                                        msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)))]). simpl.
       repeat unfold q11, q11_s, q11_s', q11_s'', q11_s''', q11_r1, q11_r2, q11_m'.
       apply IFBRANCH_M8 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
                                      msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
                                      msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
                                      bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
                                      msg ok]) (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
                                                       msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
                                                       msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)));
                                                       bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)));
                                                       msg ok]). simpl.
       repeat unfold q111, qs111, qs'111, qs''111, q111s, q111s', q111s''.
       apply IFBRANCH_M7 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
                                      msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
                                      msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
                                      bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
                                      msg ok; bol (eqm (to (x3tt 0)) (V 2));
                                      msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)))])
                                (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
                                        msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
                                        msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)));
                                        bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)));
                                        msg ok; bol (eqm (to (x3tt 1)) (V 2));
                                        msg (pk 2, (e (b 0 19) 20, sign (sk 2) (ONE, e (b 0 19) 20)))]). simpl.
       repeat unfold q111v1, q111v2, q111m, q111r1, q111r2, q111m'. simpl.
       apply IFBRANCH_M6 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
                                      msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
                                      msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
                                      bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
                                      msg ok; bol (eqm (to (x3tt 0)) (V 2));
                                      msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)));
                                      bol
                                        (eqm (to (x4ttt 0 1)) (V 2)) &
                                        (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1))); 
                                      msg ok])
                                (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
                                        msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
                                        msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)));
                                        bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)));
                                        msg ok; bol (eqm (to (x3tt 1)) (V 2));
                                        msg (pk 2, (e (b 0 19) 20, sign (sk 2) (ONE, e (b 0 19) 20)));
                                        bol
                                          (eqm (to (x4ttt 1 0)) (V 2)) &
                                          (bacc (pk 3) (b 0 19) (r 20) (pi2 (x4ttt 1 0))); 
                                        msg ok]). simpl.
       repeat unfold voter2, mnetop, mnetop', mnetop'', mnetop'''. simpl.
       apply IFBRANCH_M5 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
                                      msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
                                      msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
                                      bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
                                      msg ok; bol (eqm (to (x3tt 0)) (V 2));
                                      msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)));
                                      bol
                                        (eqm (to (x4ttt 0 1)) (V 2)) &
                                        (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1))); 
                                      msg ok; bol (eqm (to (x54t 0 1)) (V 1));
                                      msg (vtrm (sk 1) 0 7 8 (pi1 (x2t 0)) 25)])
                                (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
                                        msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
                                        msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)));
                                        bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)));
                                        msg ok; bol (eqm (to (x3tt 1)) (V 2));
                                        msg (pk 2, (e (b 0 19) 20, sign (sk 2) (ONE, e (b 0 19) 20)));
                                        bol
                                          (eqm (to (x4ttt 1 0)) (V 2)) &
                                          (bacc (pk 3) (b 0 19) (r 20) (pi2 (x4ttt 1 0))); 
                                        msg ok; bol (eqm (to (x54t 1 0)) (V 1));
                                        msg (vtrm (sk 1) 1 7 8 (pi1 (x2t 1)) 25)]). simpl.
       repeat unfold mixnet, mixnet', mixnet'', mixnet'''. repeat unfold mchecks, rev, rev''.
       apply IFBRANCH_M4 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
                                      msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
                                      msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
                                      bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
                                      msg ok; bol (eqm (to (x3tt 0)) (V 2));
                                      msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)));
                                      bol
                                        (eqm (to (x4ttt 0 1)) (V 2)) &
                                        (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1))); 
                                      msg ok; bol (eqm (to (x54t 0 1)) (V 1));
                                      msg (vtrm (sk 1) 0 7 8 (pi1 (x2t 0)) 25);
                                      bol (eqm (to (x65t 0 1)) (V 2));
                                      msg (vtrm (sk 2) 1 19 20 (pi2 (x4ttt 0 1)) 37)])
                                (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
                                        msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
                                        msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)));
                                        bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)));
                                        msg ok; bol (eqm (to (x3tt 1)) (V 2));
                                        msg (pk 2, (e (b 0 19) 20, sign (sk 2) (ONE, e (b 0 19) 20)));
                                        bol
                                          (eqm (to (x4ttt 1 0)) (V 2)) &
                                          (bacc (pk 3) (b 0 19) (r 20) (pi2 (x4ttt 1 0))); 
                                        msg ok; bol (eqm (to (x54t 1 0)) (V 1));
                                        msg (vtrm (sk 1) 1 7 8 (pi1 (x2t 1)) 25); bol (eqm (to (x65t 1 0)) (V 2));
                                        msg (vtrm (sk 2) 0 19 20 (pi2 (x4ttt 1 0)) 37)]). simpl.
       repeat unfold revtrm1, revtrm2, rev'.
       apply IFBRANCH_M3 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
                                      msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
                                      msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
                                      bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
                                      msg ok; bol (eqm (to (x3tt 0)) (V 2));
                                      msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)));
                                      bol
                                        (eqm (to (x4ttt 0 1)) (V 2)) &
                                        (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1))); 
                                      msg ok; bol (eqm (to (x54t 0 1)) (V 1));
                                      msg (vtrm (sk 1) 0 7 8 (pi1 (x2t 0)) 25);
                                      bol (eqm (to (x65t 0 1)) (V 2));
                                      msg (vtrm (sk 2) 1 19 20 (pi2 (x4ttt 0 1)) 37);
                                      bol
                                        ((eqm (to (x76t 0 1)) (pk 5)) &
                                                                      (ver (pk 1) (TWO, pi1 (pi1 (x76t 0 1))) (pi2 (pi1 (x76t 0 1))))) &
                                        (ver (pk 2) (TWO, pi1 (pi2 (x76t 0 1))) (pi2 (pi2 (x76t 0 1))));
                                      msg
                                        (shuf (dec (pi1 (pi1 (x76t 0 1))) (sk 5))
                                              (dec (pi1 (pi2 (x76t 0 1))) (sk 5)))])
                                (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
                                        msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
                                        msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)));
                                        bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)));
                                        msg ok; bol (eqm (to (x3tt 1)) (V 2));
                                        msg (pk 2, (e (b 0 19) 20, sign (sk 2) (ONE, e (b 0 19) 20)));
                                        bol
                                          (eqm (to (x4ttt 1 0)) (V 2)) &
                                          (bacc (pk 3) (b 0 19) (r 20) (pi2 (x4ttt 1 0))); 
                                        msg ok; bol (eqm (to (x54t 1 0)) (V 1));
                                        msg (vtrm (sk 1) 1 7 8 (pi1 (x2t 1)) 25); bol (eqm (to (x65t 1 0)) (V 2));
   msg (vtrm (sk 2) 0 19 20 (pi2 (x4ttt 1 0)) 37);
   bol
     ((eqm (to (x76t 1 0)) (pk 5)) &
                                   (ver (pk 1) (TWO, pi1 (pi1 (x76t 1 0))) (pi2 (pi1 (x76t 1 0))))) &
     (ver (pk 2) (TWO, pi1 (pi2 (x76t 1 0))) (pi2 (pi2 (x76t 1 0))));
   msg
     (shuf (dec (pi1 (pi1 (x76t 1 0))) (sk 5))
           (dec (pi1 (pi2 (x76t 1 0))) (sk 5)))]).
       simpl. repeat unfold ifrevtrm2, ifrevtrm2'. repeat unfold revtrm2, mixnet. repeat unfold mchecks.
       apply IFBRANCH_M2 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
                                      msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
                                      msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
                                      bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
                                      msg ok; bol (eqm (to (x3tt 0)) (V 2));
                                      msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)));
                                      bol
                                        (eqm (to (x4ttt 0 1)) (V 2)) &
                                        (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1))); 
                                      msg ok; bol (eqm (to (x54t 0 1)) (V 1));
                                      msg (vtrm (sk 1) 0 7 8 (pi1 (x2t 0)) 25);
                                      bol (eqm (to (x65t 0 1)) (V 2));
                                      msg (vtrm (sk 2) 1 19 20 (pi2 (x4ttt 0 1)) 37);
                                      bol
                                        ((eqm (to (x76t 0 1)) (pk 5)) &
                                                                      (ver (pk 1) (TWO, pi1 (pi1 (x76t 0 1))) (pi2 (pi1 (x76t 0 1))))) &
                                        (ver (pk 2) (TWO, pi1 (pi2 (x76t 0 1))) (pi2 (pi2 (x76t 0 1))));
                                      msg
                                        (shuf (dec (pi1 (pi1 (x76t 0 1))) (sk 5))
                                              (dec (pi1 (pi2 (x76t 0 1))) (sk 5)));
                                      bol (eqm (to (x87t 0 1)) (V 1));
                                      msg
                                        (enc (r 8) (pk 5) (r 51), sign (sk 1) (THREE, enc (r 8) (pk 5) (r 51)))])
                                (ml2:=  [msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
                                         msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
                                         msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)));
                                         bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)));
                                         msg ok; bol (eqm (to (x3tt 1)) (V 2));
                                         msg (pk 2, (e (b 0 19) 20, sign (sk 2) (ONE, e (b 0 19) 20)));
                                         bol
                                           (eqm (to (x4ttt 1 0)) (V 2)) &
                                           (bacc (pk 3) (b 0 19) (r 20) (pi2 (x4ttt 1 0))); 
                                         msg ok; bol (eqm (to (x54t 1 0)) (V 1));
                                         msg (vtrm (sk 1) 1 7 8 (pi1 (x2t 1)) 25); bol (eqm (to (x65t 1 0)) (V 2));
                                         msg (vtrm (sk 2) 0 19 20 (pi2 (x4ttt 1 0)) 37);
                                         bol
                                           ((eqm (to (x76t 1 0)) (pk 5)) &
                                                                         (ver (pk 1) (TWO, pi1 (pi1 (x76t 1 0))) (pi2 (pi1 (x76t 1 0))))) &
                                           (ver (pk 2) (TWO, pi1 (pi2 (x76t 1 0))) (pi2 (pi2 (x76t 1 0))));
                                         msg
                                           (shuf (dec (pi1 (pi1 (x76t 1 0))) (sk 5))
                                                 (dec (pi1 (pi2 (x76t 1 0))) (sk 5)));
                                         bol (eqm (to (x87t 1 0)) (V 1));
                                         msg
                                           (enc (r 8) (pk 5) (r 51), sign (sk 1) (THREE, enc (r 8) (pk 5) (r 51)))]). simpl.
       apply IFBRANCH_M1 with (ml1:= [msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
                                      msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
                                      msg (pk 1, (e (b 0 7) 8, sign (sk 1) (ONE, e (b 0 7) 8)));
                                      bol (eqm (to (x2t 0)) (V 1)) & (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0)));
                                      msg ok; bol (eqm (to (x3tt 0)) (V 2));
                                      msg (pk 2, (e (b 1 19) 20, sign (sk 2) (ONE, e (b 1 19) 20)));
                                      bol
                                        (eqm (to (x4ttt 0 1)) (V 2)) &
                                        (bacc (pk 3) (b 1 19) (r 20) (pi2 (x4ttt 0 1))); 
                                      msg ok; bol (eqm (to (x54t 0 1)) (V 1));
                                      msg (vtrm (sk 1) 0 7 8 (pi1 (x2t 0)) 25);
                                      bol (eqm (to (x65t 0 1)) (V 2));
                                      msg (vtrm (sk 2) 1 19 20 (pi2 (x4ttt 0 1)) 37);
                                      bol
                                        ((eqm (to (x76t 0 1)) (pk 5)) &
                                                                      (ver (pk 1) (TWO, pi1 (pi1 (x76t 0 1))) (pi2 (pi1 (x76t 0 1))))) &
                                        (ver (pk 2) (TWO, pi1 (pi2 (x76t 0 1))) (pi2 (pi2 (x76t 0 1))));
                                      msg
                                        (shuf (dec (pi1 (pi1 (x76t 0 1))) (sk 5))
                                              (dec (pi1 (pi2 (x76t 0 1))) (sk 5)));
                                      bol (eqm (to (x87t 0 1)) (V 1));
                                      msg
                                        (enc (r 8) (pk 5) (r 51), sign (sk 1) (THREE, enc (r 8) (pk 5) (r 51)));
                                      bol (eqm (to (x98t 0 1)) (V 2));
                                      msg
                                        (enc (r 20) (pk 5) (r 52),
                                         sign (sk 2) (THREE, enc (r 20) (pk 5) (r 52)))])
                                (ml2:= [msg (pk 1); msg (pk 2); msg (pk 3); msg (N 4); 
                                        msg (pk 5); msg (N 6); bol (eqm (to x1) (V 1));
                                        msg (pk 1, (e (b 1 7) 8, sign (sk 1) (ONE, e (b 1 7) 8)));
                                        bol (eqm (to (x2t 1)) (V 1)) & (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1)));
                                        msg ok; bol (eqm (to (x3tt 1)) (V 2));
                                        msg (pk 2, (e (b 0 19) 20, sign (sk 2) (ONE, e (b 0 19) 20)));
                                        bol
                                          (eqm (to (x4ttt 1 0)) (V 2)) &
                                          (bacc (pk 3) (b 0 19) (r 20) (pi2 (x4ttt 1 0))); 
                                        msg ok; bol (eqm (to (x54t 1 0)) (V 1));
   msg (vtrm (sk 1) 1 7 8 (pi1 (x2t 1)) 25); bol (eqm (to (x65t 1 0)) (V 2));
   msg (vtrm (sk 2) 0 19 20 (pi2 (x4ttt 1 0)) 37);
   bol
     ((eqm (to (x76t 1 0)) (pk 5)) &
                                   (ver (pk 1) (TWO, pi1 (pi1 (x76t 1 0))) (pi2 (pi1 (x76t 1 0))))) &
     (ver (pk 2) (TWO, pi1 (pi2 (x76t 1 0))) (pi2 (pi2 (x76t 1 0))));
   msg
     (shuf (dec (pi1 (pi1 (x76t 1 0))) (sk 5))
           (dec (pi1 (pi2 (x76t 1 0))) (sk 5)));
   bol (eqm (to (x87t 1 0)) (V 1));
   msg
     (enc (r 8) (pk 5) (r 51), sign (sk 1) (THREE, enc (r 8) (pk 5) (r 51)));
   bol (eqm (to (x98t 1 0)) (V 2));
   msg
     (enc (r 20) (pk 5) (r 52),
      sign (sk 2) (THREE, enc (r 20) (pk 5) (r 52)))]). simpl.
       (** proof of trace1 *)
       repeat unfold vtrm.
       