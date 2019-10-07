Load "frame3".
(*
(** * Frame [phi4] *)
Definition mphi3ttt n1 n2 := (phi2tt n1) ++ [msg ((pk 2), ( (e (b n2 19) 20),  (sign (sk 2) (e (b n2 19) 20))))].
Definition x4ttt n1 n2 := (f (conv_mylist_listm (mphi3ttt n1 n2))). 
Definition phi3ttft n1  := (phi2tt n1) ++ [msg  ((bsign (sk 3)  (pi1 (pi2 (pi1  (x3tt n1 ))))),  (bsign (sk 3)  (pi1 (pi2 (pi2  (x3tt n1 ))))))].
Definition x4ttft n1 := (f (conv_mylist_listm (phi3ttft n1))).

Definition phi3tftt n1 n2 := (phi2tft n1 n2) ++ [msg ok].
Definition x4tftt n1 n2 := (f (conv_mylist_listm (phi3tftt n1 n2))).

Definition phi3tftft n1 n2 := (phi2tft n1 n2) ++ [msg ok].
Definition x4tftft n1 n2 := (f (conv_mylist_listm (phi3tftft n1 n2))).

Definition phi3tftfft n1 n2 := (phi2tft n1 n2) ++ [msg  ((bsign (sk 3)  (pi1 (pi2 (pi1 (x3tft n1 n2))))),  (bsign (sk 3)  (pi1 (pi2 (pi2 (x3tft n1 n2))))))].
Definition x4tftfft n1 n2 := (f (conv_mylist_listm (phi3tftfft n1 n2))).
Definition phi3tfftt n1  := (phi2tfft n1) ++ [msg ok].
Definition x4tfftt n1  := (f (conv_mylist_listm (phi3tfftt n1))).

Definition phi3tfftft n1 n2 := (phi2tfft n1) ++ [msg ((pk 2), ( (e (b n2 21) 22),  (sign (sk 2) (e (b n2 21) 22))))].
Definition x4tfftft n1 n2 := (f (conv_mylist_listm (phi3tfftft n1 n2))).
Definition phi3fttt n1 n2 := (phi2ftt n2) ++ [msg  ((pk 1), ( (e (b n1 23) 24),  (sign (sk 1) (e (b n1 23) 24))))].

Definition x4fttt n1 n2 := (f (conv_mylist_listm (phi3fttt n1 n2))).
Definition phi3fttft  n2 := (phi2ftt n2) ++ [msg  ((bsign (sk 3)  (pi1 (pi2 (pi1 (x3ftt n2 ))))),  (bsign (sk 3)  (pi1 (pi2 (pi2 (x3ftt n2 ))))))].

Definition x4fttft n2 := (f (conv_mylist_listm (phi3fttft n2))).
Definition phi3ftftt n1 n2:= (phi2ftft n1 n2) ++ [msg ok].
Definition x4ftftt n1 n2 := (f (conv_mylist_listm (phi3ftftt n1 n2))).
Definition phi3ftftft n1 n2:= (phi2ftft n1 n2) ++ [msg ok].
Definition x4ftftft n1 n2 := (f (conv_mylist_listm (phi3ftftft n1 n2))).
Definition phi3ftftfft n1 n2:= (phi2ftft n1 n2) ++ [msg  ((bsign (sk 3)  (pi1 (pi2 (pi1 (x3ftft n1 n2))))),  (bsign (sk 3)  (pi1 (pi2 (pi2 (x3ftft n1 n2))))))].
Definition x4ftftfft n1 n2 := (f (conv_mylist_listm (phi3tftft n1 n2))).
Definition phi3ftfftt  n2 := (phi2ftfft n2) ++ [msg ok].
Definition x4ftfftt n2 := (f (conv_mylist_listm (phi3ftfftt n2))).

Definition phi3ftfftft n1 n2 := (phi2ftfft n2) ++ [msg ((pk 1), ( (e (b n1 25) 26),  (sign (sk 1) (e (b n1 25) 26))))].

Definition x4ftfftft n1 n2 := (f (conv_mylist_listm (phi3ftfftft n1 n2))).

Definition phi3ffttt n1  := (phi2fftt n1) ++ [msg ok].
Definition x4ffttt n1 := (f (conv_mylist_listm (phi3ffttt n1))).

Definition phi3ffttft n1 n2 := (phi2fftt n1) ++ [msg ((pk 2), ( (e (b n2 27) 28),  (sign (sk 2) (e (b n2 27) 28))))].
Definition x4ffttft n1 n2 := (f (conv_mylist_listm (phi3ffttft n1 n2))).

Definition phi3fftftt  n2 := (phi2fftft n2) ++ [msg ok].

Definition x4fftftt n2 := (f (conv_mylist_listm (phi3fftftt n2))).
Definition phi3fftftft n1 n2 := (phi2fftft n2) ++ [msg  ((pk 1), ( (e (b n1 29) 30),  (sign (sk 1) (e (b n1 29) 30))))].
Definition x4fftftft n1 n2 := (f (conv_mylist_listm (phi3fftftft n1 n2))).
(************************************************************************************************************************)
Definition mphi3 n1 n2 := (conv_mylist_listm (phi3 n1 n2)).
Definition x4 n1 n2 := (f (mphi3 n1 n2)). 
  
Definition q111 n1 n2 := (ifm  (eqm (to (x4ttt n1 n2)) (V 2))& (bacc (pk 3) (b n2 19) (r 20) (pi2 (x4ttt n1 n2))) ok
                                     (admin (x4ttt n1 n2))).
 
Definition q112 n1 := (ifm  (eqm (to (x4ttft n1)) (V 2))  ((pk 2), ( (e (b n1 31) 32),  (sign (sk 2) (e (b n1 31) 32)))) O).
 
 (*************************************************)                       

  
Definition q121 n1 n2 := (ifm (eqm (to (x4tftt n1 n2)) (V 2 ))& (bacc (pk 3) (b n2 11) (r 12) (pi2 (x4tftt n1 n2))) ok
                         (admin (x4tftt n1 n2))).

Definition q122 n1 n2 := (ifm (eqm (to (x4tftft n1 n2)) (V 1 ))& (bacc (pk 3) (b n1 7) (r 8) (pi1 (x4tftft n1 n2))) ok
                         (admin (x4tftft n1 n2))).
 
Definition  q123 n1 n2 := (ifm (eqm (to (x4tftfft n1 n2)) (V 1 ))& (bacc (pk 3) (b n1 7) (r 8) (pi1 (x4tftfft n1 n2))) ok
                          (ifm (eqm (to (x4tftfft n1 n2)) (V 2 ))& (bacc (pk 3) (b n2 11) (r 12) (pi2 (x4tftfft n1 n2))) ok
                               O)).
(****************************************************)

Definition q131 n1 n2 := (ifm  (eqm (to (x4tfftt n1 )) (V 2))  ((pk 2), ( (e (b n2 33) 34),  (sign (sk 2) (e (b n2 33) 34)))) O).
 
Definition q132  n1 n2:=  (ifm (eqm (to (x4tfftft n1 n2)) (V 1 ))& (bacc (pk 3) (b n1 7) (r 8) (pi1 (x4tfftft n1 n2))) ok
                          (ifm (eqm (to (x4tfftft n1 n2)) (V 2 ))& (bacc (pk 3) (b n2 21) (r 22) (pi2 (x4tfftft n1 n2))) ok
                               O)).
(****************************************************)
 
Definition q211 n1 n2 :=  (ifm (eqm (to (x4fttt n1 n2)) (V 1 ))& (bacc (pk 3) (b n1 23) (r 24) (pi1 (x4fttt n1 n2))) ok
                          (admin (x4fttt n1 n2))).

Definition q212  n2 :=  (ifm  (eqm (to (x4fttft n2)) (V 2))  ((pk 2), ( (e (b n2 35) 36),  (sign (sk 2) (e (b n2 35) 36)))) O).


(***************************************************)

Definition q221 n1 n2:=   (ifm (eqm (to (x4ftftt n1 n2)) (V 2 ))& (bacc (pk 3) (b n2 9) (r 10) (pi2 (x4ftftt n1 n2))) ok
                           (admin (x4ftftt n1 n2))).
Definition q222 n1 n2 :=  (ifm (eqm (to (x4ftftft n1 n2)) (V 1 ))& (bacc (pk 3) (b n1 13) (r 14) (pi1 (x4ftftft n1 n2))) ok                               (admin (x4ftftft n1 n2))).
Definition q223 n1 n2 := (ifm (eqm (to (x4ftftfft n1 n2)) (V 1 ))& (bacc (pk 3) (b n1 13) (r 14) (pi1 (x4ftftfft n1 n2))) ok
                         (ifm (eqm (to (x4ftftfft n1 n2)) (V 2 ))& (bacc (pk 3) (b n2 9) (r 10) (pi2 (x4ftftfft n1 n2))) ok
                              O)).

(***************************************************)

Definition q231 n1 n2 := (ifm (eqm (to (x4ftfftt n2)) (V 1))  ((pk 1), ( (e (b n1 37) 38),  (sign (sk 2) (e (b n1 37) 38)))) O).
 
Definition q232 n1 n2 := (ifm (eqm (to (x4ftfftft n1 n2)) (V 1 ))& (bacc (pk 3) (b n1 25) (r 26) (pi1 (x2 n1 n2))) ok

                              (ifm (eqm (to (x4ftfftft n1 n2)) (V 2 ))& (bacc (pk 3) (b n2 9) (r 10) (pi2 (x2 n1 n2))) ok
                               O)).
(***************************************************)

Definition q311  n1 n2 := (ifm  (eqm (to (x4ffttt n1 )) (V 2))  ((pk 2), ( (e (b n2 39) 40),  (sign (sk 2) (e (b n2 39) 40))))
                                                    O).
Definition q312 n1 n2  :=  (ifm (eqm (to (x4ffttft n1 n2)) (V 1 ))& (bacc (pk 3) (b n1 15) (r 16) (pi1 (x4ffttft n1 n2))) ok
                          (ifm (eqm (to (x4ffttft n1 n2)) (V 2 ))& (bacc (pk 3) (b n2 27) (r 28) (pi2 (x4ffttft n1 n2))) ok
                               O)).

(****************************************)

Definition q321  n1 n2 := (ifm  (eqm (to (x4fftftt n2)) (V 1))  ((pk 1), ( (e (b n1 41) 42),  (sign (sk 1) (e (b n1 41) 42)))) O).

Definition q322 n1 n2 :=  (ifm (eqm (to (x4fftftft n1 n2)) (V 1 ))& (bacc (pk 3) (b n1 29) (r 30) (pi1 (x4fftftft n1 n2))) ok
                          (ifm (eqm (to (x4fftftft n1 n2)) (V 2 ))& (bacc (pk 3) (b n2 17) (r 18) (pi2 (x4fftftft n1 n2))) ok
                               O)).

(*****************************************)
  
Definition q11_s n1 n2 :=  (ifm  (eqm (to (x3tt n1 )) (V 2)) (q111 n1 n2)
                                      (ifm (achecks (x3tt n1 )) (q112 n1 )  O)).
 
Definition q12_s n1 n2 := (ifm (eqm (to (x3tft n1 n2)) (V 1))& (bacc (pk 3) (b n1 7) (r 8) (pi2 (x3tft n1 n2))) (q121 n1 n2)
                                    (ifm (eqm (to (x3tft n1 n2)) (V 2))& (bacc (pk 3) (b n2 11) (r 12) (pi2 (x3tft n1 n2))) (q122 n1 n2)
                                                    (ifm (achecks (x3tft n1 n2)) (q123 n1 n2) O))).
 
Definition q13_s n1 n2 := (ifm (eqm (to (x3tfft n1 )) (V 1))& (bacc (pk 3) (b n1 7) (r 8) (pi2 (x3tfft n1 ))) (q131 n1 n2)
                                    (ifm  (eqm (to (x3tfft n1 )) (V 2)) (q132 n1 n2) O)).


Definition q21_s n1 n2 := (ifm  (eqm (to (x3ftt n2)) (V 1))  (q211 n1 n2)
                                   (ifm (achecks (x3ftt n2)) (q212  n2) O)).

Definition q22_s n1 n2  := (ifm (eqm (to (x3ftft n1 n2)) (V 1))& (bacc (pk 3) (b n1 13) (r 14) (pi1 (x3ftft n1 n2))) (q221 n1 n2)
                                    (ifm (eqm (to (x3ftft n1 n2)) (V 2))& (bacc (pk 3) (b n2 9) (r 10) (pi2 (x3ftft n1 n2))) (q222 n1 n2)
                                                   (ifm (achecks (x3ftft n1 n2)) (q223 n1 n2) O))).
 
Definition q23_s n1 n2 := (ifm (eqm (to (x3ftfft  n2)) (V 2))& (bacc (pk 3) (b n2 9) (r 10) (pi2 (x3ftfft n2))) (q231 n1 n2)
                        (ifm  (eqm (to (x3ftfft  n2)) (V 1))  (q232 n1 n2) O)).

 
Definition q31_s n1 n2 := (ifm (eqm (to (x3fftt n1 )) (V 1))& (bacc (pk 3) (b n1 15) (r 16) (pi1 (x3fftt n1 ))) (q311 n1 n2)
                                    (ifm  (eqm (to (x3fftt n1 )) (V 2))  (q312 n1 n2) O)).

Definition q32_s n1 n2 := (ifm (eqm (to (x3fftft  n2)) (V 2))& (bacc (pk 3) (b n2 17) (r 18) (pi2 (x3fftft n2))) (q321 n1 n2)
                                    (ifm  (eqm (to (x3fftft  n2)) (V 1)) (q322 n1 n2) O)).
(********************************************************************************************)

Definition q1_ss n1 n2 := (ifm (eqm (to (x2t n1 )) (V 1))& (bacc (pk 3) (b n1 7) (r 8) (pi1 (x2t n1 )))  (q11_s n1 n2)
			           (ifm (eqm (to (x2t n1 )) (V 2))  (q12_s n1 n2)
                                                  (ifm (achecks (x2t n1 )) (q13_s n1 n2) O))).
 
Definition q2_ss n1 n2 :=  (ifm (eqm (to (x2ft n2)) (V 2))& (bacc (pk 3) (b n2 9) (r 10) (pi2 (x2ft n2)))  (q21_s n1 n2)
			           (ifm (eqm (to (x2ft n2)) (V 1))  (q22_s n1 n2)
                                                   (ifm (achecks (x2ft n2)) (q23_s n1 n2) O))).
 
Definition q3_ss n1 n2 := (ifm (eqm (to (x2fft)) (V 1)) (q31_s n1 n2)
		    	            (ifm  (eqm (to (x2fft )) (V 2))  (q32_s n1 n2) O)).


Definition t3 n1 n2 :=  (ifm (eqm (to x1) (V 1)) (q1_ss n1 n2)
		    	           (ifm (eqm (to x1) (V 2))  (q2_ss n1 n2)
                                                   (ifm (achecks x1) (q3_ss n1 n2)
                                                                   O))).

Definition phi4 n1 n2 := (phi3 n1 n2) ++ [msg (t3 n1 n2)] .

(*

Theorem frame4ind : (phi4 0 1) ~ (phi4 1 0).
Proof.  unfold phi4, phi3. unfold t2, t3. simpl.
        unfold q1_s, q2_s, q3_s. unfold q1_ss, q2_ss, q3_ss.
        repeat unf.
repeat unfold admin, achecks.
  ufcma_pi1 x1.  
ufcma_pi1 (x2t 0).
ufcma_pi2 (x2t 0).
ufcma_pi1 (x2ft 1). 
ufcma_pi2 (x2ft 0). 
ufcma_pi1 (x2t 1).
ufcma_pi2 (x2t 1).
ufcma_pi1 (x2ft 0). 
repeat aply_andB_elm.   
repeat (rew_mupbver;aply_bver; rew_hyps; try split; try reflexivity).

repeat unfold q11_s, q21_s. repeat unf.  unfold q12_s, q22_s.
repeat unfold q111, q112, q121, q122, q123, q121, q132, q211, q212, q221, q222, q223, q231, q232, q311, q312, q321, q322; repeat unfold q11, q12, q13, q21, q22, q23, q31, q32. repeat unf.
repeat unfold admin, achecks.  
ufcma_pi1 (x3ftft 0 1);
ufcma_pi2 (x3ftft 0 1);
ufcma_pi1 (x3ftft 1 0);
ufcma_pi2 (x3ftft 1 0).
Ltac unforge x1 n1 n2:=
  ufcma_pi1 (x1 n1 n2); ufcma_pi2 (x1 n1 n2);   ufcma_pi1 (x1 n2 n1);   ufcma_pi2 (x1 n2 n1).
unforge x3tft 0 1 .
unforge x4tftft 0 1. 
unforge x4ftftt 0 1.
apply IFBRANCH_M4 with (ml1:= (phi0)) (ml2:= phi0).
simpl.
repeat aply_andB_elm.

apply IFBRANCH_M3 with (ml1:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8)))]) (ml2:=  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (e (b 1 7) 8)))]).
simpl.
apply IFBRANCH_M2 with (ml1:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8)));
    bol (eqm (to (x2t 0)) (V 2));
    msg (pk 2, (e (b 1 11) 12, sign (sk 2) (e (b 1 11) 12)))]) (ml2:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (e (b 1 7) 8)));
   bol (eqm (to (x2t 1)) (V 2));
   msg (pk 2, (e (b 0 11) 12, sign (sk 2) (e (b 0 11) 12)))]).
simpl. 
repeat (rew_mupbver;aply_bver; rew_hyps; try split; try reflexivity).
  aply_blindness 3 8 12 0 1 (b 0 7) (b 1 11)  ((Mvar 0), (Mvar 1)) ((Mvar 0), (Mvar 1))  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                                                       msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); msg (sk 3) ] ; simpl;
aplyprojn 1 16 H; try split; try reflexivity;
rep_commits 0 1 11 21 7 22 fr1 fr2 temp H H0;
rename H0 into H;
appconst H;
x1checks x1 x1 H;
funapp_vtrm 1 0 1 7 8 H;
funapp_vtrm 2 1 0 11 12 H.
x1checks (x2t 0 ) (x2t 1) H.
x1checks (x3tft 0 1) (x3tft 1 0) H. 
adminchecks (x3tft 0 1) (x3tft 1 0) H. 
Ltac ver_suc1 n x1 e1 x2 e2 H:=
  funapptrmhyp (bol (eqm (pi1 (pi2 x1)) e1)) (bol (eqm (pi1 (pi2 x2)) e2)) H;
  funapptrmhyp (bol  (ver (pk n) e1 (pi2 (pi2 x1))))  (bol (ver (pk n) e2 (pi2 (pi2 x2)))) H.
 
ver_suc1 2 (pi2 (x3tft 0 1)) (e (b 1 11) 12) (pi2 (x3tft 1 0)) (e (b 0 11) 12) H.
  funapptrmhyp (msg (ifm
                     (ver (pk 2) (e (b 1 11) 12)
                        (pi2 (pi2 (pi2 (x3tft 0 1)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 0 1)))),
                     bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 0 1))))) O)) (msg    (ifm
                     (ver (pk 2) (e (b 0 11) 12)
                        (pi2 (pi2 (pi2 (x3tft 1 0)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 1 0)))),
                      bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 1 0))))) O)) H.
  funapptrmhyp (msg  (ifm (eqm (pi1 (pi2 (pi2 (x3tft 0 1)))) (e (b 1 11) 12)) (ifm
                     (ver (pk 2) (e (b 1 11) 12)
                        (pi2 (pi2 (pi2 (x3tft 0 1)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 0 1)))),
                     bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 0 1))))) O) O)) (msg  (ifm (eqm (pi1 (pi2 (pi2 (x3tft 1 0)))) (e (b 0 11) 12))  (ifm (ver (pk 2) (e (b 0 11) 12) (pi2 (pi2 (pi2 (x3tft 1 0))))) (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 1 0)))),
                                                                                                                                                                                                         bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 1 0))))) O) O)) H.

  ver_suc1 1 (pi1 (x3tft 0 1)) (e (b 0 7) 8) (pi1 (x3tft 1 0)) (e (b 1 7) 8) H.
  funapptrmhyp (msg  (ifm (ver (pk 1) (e (b 0 7) 8) (pi2 (pi2 (pi1 (x3tft 0 1)))))
               (ifm (eqm (pi1 (pi2 (pi2 (x3tft 0 1)))) (e (b 1 11) 12))
                  (ifm
                     (ver (pk 2) (e (b 1 11) 12)
                        (pi2 (pi2 (pi2 (x3tft 0 1)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 0 1)))),
                     bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 0 1))))) O) O) O)) (msg  (ifm (ver (pk 1) (e (b 1 7) 8) (pi2 (pi2 (pi1 (x3tft 1 0)))))
               (ifm (eqm (pi1 (pi2 (pi2 (x3tft 1 0)))) (e (b 0 11) 12))
                  (ifm
                     (ver (pk 2) (e (b 0 11) 12)
                        (pi2 (pi2 (pi2 (x3tft 1 0)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 1 0)))),
                      bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 1 0))))) O) O) O)) H.
funapptrmhyp (msg   (ifm (eqm (pi1 (pi2 (pi1 (x3tft 0 1)))) (e (b 0 7) 8))
            (ifm (ver (pk 1) (e (b 0 7) 8) (pi2 (pi2 (pi1 (x3tft 0 1)))))
               (ifm (eqm (pi1 (pi2 (pi2 (x3tft 0 1)))) (e (b 1 11) 12))
                  (ifm
                     (ver (pk 2) (e (b 1 11) 12)
                        (pi2 (pi2 (pi2 (x3tft 0 1)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 0 1)))),
                     bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 0 1))))) O) O) O) O)) (msg  (ifm (eqm (pi1 (pi2 (pi1 (x3tft 1 0)))) (e (b 1 7) 8))
            (ifm (ver (pk 1) (e (b 1 7) 8) (pi2 (pi2 (pi1 (x3tft 1 0)))))
               (ifm (eqm (pi1 (pi2 (pi2 (x3tft 1 0)))) (e (b 0 11) 12))
                  (ifm
                     (ver (pk 2) (e (b 0 11) 12)
                        (pi2 (pi2 (pi2 (x3tft 1 0)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 1 0)))),
                      bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 1 0))))) O) O) O) O)) H.

funapptrmhyp  (msg
      (ifm (eqm (to (x3tft 0 1)) (pk 3))
         (ifm (eqm (pi1 (pi2 (pi1 (x3tft 0 1)))) (e (b 0 7) 8))
            (ifm (ver (pk 1) (e (b 0 7) 8) (pi2 (pi2 (pi1 (x3tft 0 1)))))
               (ifm (eqm (pi1 (pi2 (pi2 (x3tft 0 1)))) (e (b 1 11) 12))
                  (ifm
                     (ver (pk 2) (e (b 1 11) 12)
                        (pi2 (pi2 (pi2 (x3tft 0 1)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 0 1)))),
                     bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 0 1))))) O) O) O) O)
         O))  (msg
     (ifm (eqm (to (x3tft 1 0)) (pk 3))
        (ifm (eqm (pi1 (pi2 (pi1 (x3tft 1 0)))) (e (b 1 7) 8))
           (ifm (ver (pk 1) (e (b 1 7) 8) (pi2 (pi2 (pi1 (x3tft 1 0)))))
              (ifm (eqm (pi1 (pi2 (pi2 (x3tft 1 0)))) (e (b 0 11) 12))
                 (ifm
                    (ver (pk 2) (e (b 0 11) 12) (pi2 (pi2 (pi2 (x3tft 1 0)))))
                    (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 1 0)))),
                     bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 1 0))))) O) O) O) O) O)) H.

restrsublis H.
(** subgoal *)
simpl.
apply IFBRANCH_M2 with (ml1:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8)));
    bol (eqm (to (x2t 0)) (V 2));
    msg (pk 2, (e (b 1 11) 12, sign (sk 2) (e (b 1 11) 12)));
    bol (eqm (to (x3tft 0 1)) (V 1))]) (ml2:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (e (b 1 7) 8)));
   bol (eqm (to (x2t 1)) (V 2));
   msg (pk 2, (e (b 0 11) 12, sign (sk 2) (e (b 0 11) 12)));
   bol (eqm (to (x3tft 1 0)) (V 1))]). simpl.
repeat (rew_mupbver;aply_bver; rew_hyps; try split; try reflexivity).

 aply_blindness 3 8 12 0 1 (b 0 7) (b 1 11)  ((Mvar 0), (Mvar 1)) ((Mvar 0), (Mvar 1))  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                                                       msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); msg (sk 3) ] ; simpl;
aplyprojn 1 16 H; try split; try reflexivity;
rep_commits 0 1 11 21 7 22 fr1 fr2 temp H H0;
rename H0 into H;
appconst H;
x1checks x1 x1 H;
funapp_vtrm 1 0 1 7 8 H;
funapp_vtrm 2 1 0 11 12 H.
x1checks (x2t 0 ) (x2t 1) H.
x1checks (x3tft 0 1) (x3tft 1 0) H. 
adminchecks (x3tft 0 1) (x3tft 1 0) H. 
 
ver_suc1 2 (pi2 (x3tft 0 1)) (e (b 1 11) 12) (pi2 (x3tft 1 0)) (e (b 0 11) 12) H.
  funapptrmhyp (msg (ifm
                     (ver (pk 2) (e (b 1 11) 12)
                        (pi2 (pi2 (pi2 (x3tft 0 1)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 0 1)))),
                     bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 0 1))))) O)) (msg    (ifm
                     (ver (pk 2) (e (b 0 11) 12)
                        (pi2 (pi2 (pi2 (x3tft 1 0)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 1 0)))),
                      bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 1 0))))) O)) H.
  funapptrmhyp (msg  (ifm (eqm (pi1 (pi2 (pi2 (x3tft 0 1)))) (e (b 1 11) 12)) (ifm
                     (ver (pk 2) (e (b 1 11) 12)
                        (pi2 (pi2 (pi2 (x3tft 0 1)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 0 1)))),
                     bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 0 1))))) O) O)) (msg  (ifm (eqm (pi1 (pi2 (pi2 (x3tft 1 0)))) (e (b 0 11) 12))  (ifm (ver (pk 2) (e (b 0 11) 12) (pi2 (pi2 (pi2 (x3tft 1 0))))) (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 1 0)))),
                                                                                                                                                                                                         bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 1 0))))) O) O)) H.

  ver_suc1 1 (pi1 (x3tft 0 1)) (e (b 0 7) 8) (pi1 (x3tft 1 0)) (e (b 1 7) 8) H.
  funapptrmhyp (msg  (ifm (ver (pk 1) (e (b 0 7) 8) (pi2 (pi2 (pi1 (x3tft 0 1)))))
               (ifm (eqm (pi1 (pi2 (pi2 (x3tft 0 1)))) (e (b 1 11) 12))
                  (ifm
                     (ver (pk 2) (e (b 1 11) 12)
                        (pi2 (pi2 (pi2 (x3tft 0 1)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 0 1)))),
                     bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 0 1))))) O) O) O)) (msg  (ifm (ver (pk 1) (e (b 1 7) 8) (pi2 (pi2 (pi1 (x3tft 1 0)))))
               (ifm (eqm (pi1 (pi2 (pi2 (x3tft 1 0)))) (e (b 0 11) 12))
                  (ifm
                     (ver (pk 2) (e (b 0 11) 12)
                        (pi2 (pi2 (pi2 (x3tft 1 0)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 1 0)))),
                      bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 1 0))))) O) O) O)) H.
funapptrmhyp (msg   (ifm (eqm (pi1 (pi2 (pi1 (x3tft 0 1)))) (e (b 0 7) 8))
            (ifm (ver (pk 1) (e (b 0 7) 8) (pi2 (pi2 (pi1 (x3tft 0 1)))))
               (ifm (eqm (pi1 (pi2 (pi2 (x3tft 0 1)))) (e (b 1 11) 12))
                  (ifm
                     (ver (pk 2) (e (b 1 11) 12)
                        (pi2 (pi2 (pi2 (x3tft 0 1)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 0 1)))),
                     bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 0 1))))) O) O) O) O)) (msg  (ifm (eqm (pi1 (pi2 (pi1 (x3tft 1 0)))) (e (b 1 7) 8))
            (ifm (ver (pk 1) (e (b 1 7) 8) (pi2 (pi2 (pi1 (x3tft 1 0)))))
               (ifm (eqm (pi1 (pi2 (pi2 (x3tft 1 0)))) (e (b 0 11) 12))
                  (ifm
                     (ver (pk 2) (e (b 0 11) 12)
                        (pi2 (pi2 (pi2 (x3tft 1 0)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 1 0)))),
                      bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 1 0))))) O) O) O) O)) H.

funapptrmhyp  (msg
      (ifm (eqm (to (x3tft 0 1)) (pk 3))
         (ifm (eqm (pi1 (pi2 (pi1 (x3tft 0 1)))) (e (b 0 7) 8))
            (ifm (ver (pk 1) (e (b 0 7) 8) (pi2 (pi2 (pi1 (x3tft 0 1)))))
               (ifm (eqm (pi1 (pi2 (pi2 (x3tft 0 1)))) (e (b 1 11) 12))
                  (ifm
                     (ver (pk 2) (e (b 1 11) 12)
                        (pi2 (pi2 (pi2 (x3tft 0 1)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 0 1)))),
                     bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 0 1))))) O) O) O) O)
         O))  (msg
     (ifm (eqm (to (x3tft 1 0)) (pk 3))
        (ifm (eqm (pi1 (pi2 (pi1 (x3tft 1 0)))) (e (b 1 7) 8))
           (ifm (ver (pk 1) (e (b 1 7) 8) (pi2 (pi2 (pi1 (x3tft 1 0)))))
              (ifm (eqm (pi1 (pi2 (pi2 (x3tft 1 0)))) (e (b 0 11) 12))
                 (ifm
                    (ver (pk 2) (e (b 0 11) 12) (pi2 (pi2 (pi2 (x3tft 1 0)))))
                    (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 1 0)))),
                     bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 1 0))))) O) O) O) O) O)) H.

restrsublis H.
(** subgoal *)

simpl.
apply IFBRANCH_M2 with (ml1:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8)));
    bol (eqm (to (x2t 0)) (V 2));
    msg (pk 2, (e (b 1 11) 12, sign (sk 2) (e (b 1 11) 12)));
    bol (eqm (to (x3tft 0 1)) (V 1)); bol (eqm (to (x3tft 0 1)) (V 2))]) (ml2:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (e (b 1 7) 8)));
   bol (eqm (to (x2t 1)) (V 2));
   msg (pk 2, (e (b 0 11) 12, sign (sk 2) (e (b 0 11) 12)));
   bol (eqm (to (x3tft 1 0)) (V 1)); bol (eqm (to (x3tft 1 0)) (V 2))]). simpl.
repeat (rew_mupbver;aply_bver; rew_hyps; try split; try reflexivity).
 aply_blindness 3 8 12 0 1 (b 0 7) (b 1 11)  ((Mvar 0), (Mvar 1)) ((Mvar 0), (Mvar 1))  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                                                       msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); msg (sk 3) ] ; simpl;
aplyprojn 1 16 H; try split; try reflexivity;
rep_commits 0 1 11 21 7 22 fr1 fr2 temp H H0;
rename H0 into H;
appconst H;
x1checks x1 x1 H;
funapp_vtrm 1 0 1 7 8 H;
funapp_vtrm 2 1 0 11 12 H.
x1checks (x2t 0 ) (x2t 1) H.
x1checks (x3tft 0 1) (x3tft 1 0) H. 
adminchecks (x3tft 0 1) (x3tft 1 0) H. 
 
ver_suc1 2 (pi2 (x3tft 0 1)) (e (b 1 11) 12) (pi2 (x3tft 1 0)) (e (b 0 11) 12) H.
  funapptrmhyp (msg (ifm
                     (ver (pk 2) (e (b 1 11) 12)
                        (pi2 (pi2 (pi2 (x3tft 0 1)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 0 1)))),
                     bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 0 1))))) O)) (msg    (ifm
                     (ver (pk 2) (e (b 0 11) 12)
                        (pi2 (pi2 (pi2 (x3tft 1 0)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 1 0)))),
                      bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 1 0))))) O)) H.
  funapptrmhyp (msg  (ifm (eqm (pi1 (pi2 (pi2 (x3tft 0 1)))) (e (b 1 11) 12)) (ifm
                     (ver (pk 2) (e (b 1 11) 12)
                        (pi2 (pi2 (pi2 (x3tft 0 1)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 0 1)))),
                     bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 0 1))))) O) O)) (msg  (ifm (eqm (pi1 (pi2 (pi2 (x3tft 1 0)))) (e (b 0 11) 12))  (ifm (ver (pk 2) (e (b 0 11) 12) (pi2 (pi2 (pi2 (x3tft 1 0))))) (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 1 0)))),
                                                                                                                                                                                                         bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 1 0))))) O) O)) H.

  ver_suc1 1 (pi1 (x3tft 0 1)) (e (b 0 7) 8) (pi1 (x3tft 1 0)) (e (b 1 7) 8) H.
  funapptrmhyp (msg  (ifm (ver (pk 1) (e (b 0 7) 8) (pi2 (pi2 (pi1 (x3tft 0 1)))))
               (ifm (eqm (pi1 (pi2 (pi2 (x3tft 0 1)))) (e (b 1 11) 12))
                  (ifm
                     (ver (pk 2) (e (b 1 11) 12)
                        (pi2 (pi2 (pi2 (x3tft 0 1)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 0 1)))),
                     bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 0 1))))) O) O) O)) (msg  (ifm (ver (pk 1) (e (b 1 7) 8) (pi2 (pi2 (pi1 (x3tft 1 0)))))
               (ifm (eqm (pi1 (pi2 (pi2 (x3tft 1 0)))) (e (b 0 11) 12))
                  (ifm
                     (ver (pk 2) (e (b 0 11) 12)
                        (pi2 (pi2 (pi2 (x3tft 1 0)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 1 0)))),
                      bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 1 0))))) O) O) O)) H.
funapptrmhyp (msg   (ifm (eqm (pi1 (pi2 (pi1 (x3tft 0 1)))) (e (b 0 7) 8))
            (ifm (ver (pk 1) (e (b 0 7) 8) (pi2 (pi2 (pi1 (x3tft 0 1)))))
               (ifm (eqm (pi1 (pi2 (pi2 (x3tft 0 1)))) (e (b 1 11) 12))
                  (ifm
                     (ver (pk 2) (e (b 1 11) 12)
                        (pi2 (pi2 (pi2 (x3tft 0 1)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 0 1)))),
                     bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 0 1))))) O) O) O) O)) (msg  (ifm (eqm (pi1 (pi2 (pi1 (x3tft 1 0)))) (e (b 1 7) 8))
            (ifm (ver (pk 1) (e (b 1 7) 8) (pi2 (pi2 (pi1 (x3tft 1 0)))))
               (ifm (eqm (pi1 (pi2 (pi2 (x3tft 1 0)))) (e (b 0 11) 12))
                  (ifm
                     (ver (pk 2) (e (b 0 11) 12)
                        (pi2 (pi2 (pi2 (x3tft 1 0)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 1 0)))),
                      bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 1 0))))) O) O) O) O)) H.
restrsublis H.
(** subgoal *)

  (aply_blindness 3 8 12 0 1 (b 0 7) (b 1 11)  ((Mvar 0), (Mvar 1)) ((Mvar 0), (Mvar 1))  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                                                       msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); msg (sk 3) ] ; simpl;
aplyprojn 1 16 H; try split; try reflexivity;
rep_commits 0 1 11 21 7 22 fr1 fr2 temp H H0;
rename H0 into H;
appconst H;
x1checks x1 x1 H;
funapp_vtrm 1 0 1 7 8 H;
funapp_vtrm 2 1 0 11 12 H;
x1checks (x2t 0 ) (x2t 1) H;
x1checks (x3tft 0 1) (x3tft 1 0) H;
restrsublis H).
 aply_blindness 3 8 12 0 1 (b 0 7) (b 1 11)  ((Mvar 0), (Mvar 1)) ((Mvar 0), (Mvar 1))  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                                                       msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); msg (sk 3) ] ; simpl;
aplyprojn 1 16 H; try split; try reflexivity;
rep_commits 0 1 11 21 7 22 fr1 fr2 temp H H0;
rename H0 into H;
appconst H;
x1checks x1 x1 H;
funapp_vtrm 1 0 1 7 8 H;
funapp_vtrm 2 1 0 11 12 H;
x1checks (x2t 0 ) (x2t 1) H;
x1checks (x3tft 0 1) (x3tft 1 0) H;
restrsublis H.
 (** subgoal *)
 simpl.
 apply IFBRANCH_M4 with (ml1:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1))]) (ml2:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                             msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1))]). simpl.
 apply IFBRANCH_M3 with (ml1:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1)); 
    bol (eqm (to x1) (V 2));
    msg (pk 2, (e (b 1 9) 10, sign (sk 2) (e (b 1 9) 10)))]) (ml2:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1)); 
   bol (eqm (to x1) (V 2));
   msg (pk 2, (e (b 0 9) 10, sign (sk 2) (e (b 0 9) 10)))]). simpl.
 repeat aply_andB_elm.
 repeat (rew_mupbver;aply_bver; rew_hyps; try split; try reflexivity).
 
 aply_blindness 3 10 14 0 1 (b 1 9) (b 0 13)  ((Mvar 0), (Mvar 1)) ((Mvar 0), (Mvar 1))  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                                                       msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); msg (sk 3) ] ; simpl;
aplyprojn 1 16 H; try split; try reflexivity.
rep_commits 1 0 13 30 9 31 fr1 fr2 temp H H0.
rename H0 into H;
appconst H;
x1checks x1 x1 H;
funapp_vtrm 2 1 0 9 10 H;
funapp_vtrm 1 0 1 13 14 H.
x1checks (x2ft 1) (x2ft 0) H.
x1checks (x3ftft 0 1) (x3ftft 1 0) H. 
adminchecks (x3ftft 0 1) (x3ftft 1 0) H. 
 
ver_suc1 2 (pi2 (x3ftft 0 1)) (e (b 1 9) 10) (pi2 (x3ftft 1 0)) (e (b 0 9) 10) H.
  funapptrmhyp (msg (ifm
                     (ver (pk 2) (e (b 1 9) 10)
                        (pi2 (pi2 (pi2 (x3ftft 0 1)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3ftft 0 1)))),
                     bsign (sk 3) (pi1 (pi2 (pi2 (x3ftft 0 1))))) O))  (msg    (ifm
                     (ver (pk 2) (e (b 0 9) 10)
                        (pi2 (pi2 (pi2 (x3ftft 1 0)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3ftft 1 0)))),
                      bsign (sk 3) (pi1 (pi2 (pi2 (x3ftft 1 0))))) O)) H.
   funapptrmhyp (msg  (ifm (eqm (pi1 (pi2 (pi2 (x3ftft 0 1)))) (e (b 1 9) 10)) (ifm
                     (ver (pk 2) (e (b 1 9) 10)
                        (pi2 (pi2 (pi2 (x3ftft 0 1)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3ftft 0 1)))),
                     bsign (sk 3) (pi1 (pi2 (pi2 (x3ftft 0 1))))) O) O)) (msg  (ifm (eqm (pi1 (pi2 (pi2 (x3ftft 1 0)))) (e (b 0 9) 10))  (ifm (ver (pk 2) (e (b 0 9) 10) (pi2 (pi2 (pi2 (x3ftft 1 0))))) (bsign (sk 3) (pi1 (pi2 (pi1 (x3ftft 1 0)))),
                                                                                                                                                                                                         bsign (sk 3) (pi1 (pi2 (pi2 (x3ftft 1 0))))) O) O)) H.

   ver_suc1 1 (pi1 (x3ftft 0 1)) (e (b 0 13) 14) (pi1 (x3ftft 1 0)) (e (b 1 13) 14) H.

 funapptrmhyp (msg  (ifm (ver (pk 1) (e (b 0 13) 14) (pi2 (pi2 (pi1 (x3ftft 0 1))))) (ifm (eqm (pi1 (pi2 (pi2 (x3ftft 0 1)))) (e (b 1 9) 10)) (ifm
                     (ver (pk 2) (e (b 1 9) 10)
                        (pi2 (pi2 (pi2 (x3ftft 0 1)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3ftft 0 1)))),
                     bsign (sk 3) (pi1 (pi2 (pi2 (x3ftft 0 1))))) O) O) O)) (msg (ifm (ver (pk 1) (e (b 1 13) 14) (pi2 (pi2 (pi1 (x3ftft 1 0)))))  (ifm (eqm (pi1 (pi2 (pi2 (x3ftft 1 0)))) (e (b 0 9) 10))  (ifm (ver (pk 2) (e (b 0 9) 10) (pi2 (pi2 (pi2 (x3ftft 1 0))))) (bsign (sk 3) (pi1 (pi2 (pi1 (x3ftft 1 0)))),
                                                                                                                                                                                                         bsign (sk 3) (pi1 (pi2 (pi2 (x3ftft 1 0))))) O) O) O)) H.
   funapptrmhyp  (msg
              (ifm (eqm (pi1 (pi2 (pi1 (x3ftft 0 1)))) (e (b 0 13) 14))
            (ifm (ver (pk 1) (e (b 0 13) 14) (pi2 (pi2 (pi1 (x3ftft 0 1)))))
               (ifm (eqm (pi1 (pi2 (pi2 (x3ftft 0 1)))) (e (b 1 9) 10))
                  (ifm
                     (ver (pk 2) (e (b 1 9) 10)
                        (pi2 (pi2 (pi2 (x3ftft 0 1)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3ftft 0 1)))),
                     bsign (sk 3) (pi1 (pi2 (pi2 (x3ftft 0 1))))) O) O) O) O))
           (msg
               (ifm (eqm (pi1 (pi2 (pi1 (x3ftft 1 0)))) (e (b 1 13) 14))
            (ifm (ver (pk 1) (e (b 1 13) 14) (pi2 (pi2 (pi1 (x3ftft 1 0)))))
               (ifm (eqm (pi1 (pi2 (pi2 (x3ftft 1 0)))) (e (b 0 9) 10))
                  (ifm
                     (ver (pk 2) (e (b 0 9) 10)
                        (pi2 (pi2 (pi2 (x3ftft 1 0)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3ftft 1 0)))),
                     bsign (sk 3) (pi1 (pi2 (pi2 (x3ftft 1 0))))) O) O) O) O))
          H.
  funapptrmhyp  (msg
      (ifm (eqm (to (x3ftft 0 1)) (pk 3)) 
         (ifm (eqm (pi1 (pi2 (pi1 (x3ftft 0 1)))) (e (b 0 13) 14))
            (ifm (ver (pk 1) (e (b 0 13) 14) (pi2 (pi2 (pi1 (x3ftft 0 1)))))
               (ifm (eqm (pi1 (pi2 (pi2 (x3ftft 0 1)))) (e (b 1 9) 10))
                  (ifm
                     (ver (pk 2) (e (b 1 9) 10)
                        (pi2 (pi2 (pi2 (x3ftft 0 1)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3ftft 0 1)))),
                     bsign (sk 3) (pi1 (pi2 (pi2 (x3ftft 0 1))))) O) O) O) O)
         O))   (msg
      (ifm (eqm (to (x3ftft 1 0)) (pk 3))
         (ifm (eqm (pi1 (pi2 (pi1 (x3ftft 1 0)))) (e (b 1 13) 14))
            (ifm (ver (pk 1) (e (b 1 13) 14) (pi2 (pi2 (pi1 (x3ftft 1 0)))))
               (ifm (eqm (pi1 (pi2 (pi2 (x3ftft 1 0)))) (e (b 0 9) 10))
                  (ifm
                     (ver (pk 2) (e (b 0 9) 10)
                        (pi2 (pi2 (pi2 (x3ftft 1 0)))))
                     (bsign (sk 3) (pi1 (pi2 (pi1 (x3ftft 1 0)))),
                     bsign (sk 3) (pi1 (pi2 (pi2 (x3ftft 1 0))))) O) O) O) O)
         O)) H.
  restrsublis H.
(** subgoal *)
  simpl.
aply_blindness 3 10 11 0 1 (b 1 9) (b 0 9)  ((Mvar 0), (Mvar 1)) ((Mvar 0), (Mvar 1))  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                                                       msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); msg (sk 3) ] ; simpl;
aplyprojn 2 15 H; try split; try reflexivity;
appconst H;
x1checks x1 x1 H;
funapp_vtrm 2 1 0 9 10 H;
x1checks (x2ft 1 ) (x2ft 0) H;
restrsublis H.
reflexivity.
Qed. *)

End foo_prot2. *)
