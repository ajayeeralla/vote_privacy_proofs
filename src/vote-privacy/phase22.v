   Load "phase21".
 
(** some tactics *)

 
(*******************************************)
(** ** Phase-II : Voting Phase *)
 
(** 
- (V) -> C : sign( sk (A) , commit(v, r)) 

 *)
(** frame 6***)
  (** * Frame [phi6] *)
  
  Definition phi55t n1 n2 := (mphi44t n1 n2) ++  [msg (vtrm (sk 1) n1 7 8 (pi1 (x2t n1)) 25)].
  
Definition x65t n1 n2 := (f (conv_mylist_listm (phi55t n1 n2))).

Definition phi54tft n1 n2 := (mphi44t n1 n2) ++ [msg (vtrm (sk 2) n2 19 20 (pi2 (x4ttt n1 n2)) 26) ].
Definition x64tft n1 n2 := (f (conv_mylist_listm (phi54tft n1 n2))). 
(*
Definition phi3ttft n1  := (phi2tt n1) ++ [msg  ((bsign (sk 3)  (pi1 (pi2 (pi1  (x3tt n1 ))))),  (bsign (sk 3)  (pi1 (pi2 (pi2  (x3tt n1 ))))))].
Definition x4ttft n1 := (f (conv_mylist_listm (phi3ttft n1))).
*)
Definition phi5tf4t n1 n2 := (phi4tf3t n1 n2) ++ [msg (vtrm (sk 1) n1 7 8 (pi1 (x3tft n1 n2)) 27)].
Definition x6tf4t n1 n2 := (f (conv_mylist_listm (phi5tf4t n1 n2))).

Definition phi5tf3tft n1 n2 := (phi4tf3t n1 n2) ++ [msg (vtrm (sk 2) n2 11 12 (pi2 (x4tftt n1 n2)) 28)].
Definition x6tf3tft n1 n2 := (f (conv_mylist_listm (phi5tf3tft n1 n2))).
(**********************************************************************************)
 
Definition phi5tftf3t n1 n2 := (phi4tftftt n1 n2) ++ [msg (vtrm (sk 1) n1 7 8 (pi1 (x4tftft n1 n2)) 29)].
Definition x6tftf3t n1 n2 := (f (conv_mylist_listm (phi5tftf3t n1 n2))).

Definition phi5tftfttft n1 n2 := (phi4tftftt n1 n2) ++ [msg (vtrm (sk 2) n2 11 12 (pi2 (x3tft n1 n2)) 30)].
Definition x6tftfttft n1 n2 := (f (conv_mylist_listm (phi5tftfttft n1 n2))).
(*
Definition phi3tftfft n1 n2 := (phi2tft n1 n2) ++ [msg  ((bsign (sk 3)  (pi1 (pi2 (pi1 (x3tft n1 n2))))),  (bsign (sk 3)  (pi1 (pi2 (pi2 (x3tft n1 n2))))))].

Definition x4tftfft n1 n2 := (f (conv_mylist_listm (phi3tftfft n1 n2))).
 *)
(*
Definition phi3tfftt n1  := (phi2tfft n1) ++ [msg ok].
Definition x4tfftt n1  := (f (conv_mylist_listm (phi3tfftt n1))).

Definition phi3tfftft n1 n2 := (phi2tfft n1) ++ [msg ((pk 2), ( (e (b n2 21) 22),  (sign (sk 2) (e (b n2 21) 22))))].
Definition x4tfftft n1 n2 := (f (conv_mylist_listm (phi3tfftft n1 n2))). *)
Definition phi5f5t n1 n2 := (phi4f4t n1 n2) ++ [msg (vtrm (sk 1) n1 23 24 (pi1 (x4fttt n1 n2)) 31)].
Definition x6f5t n1 n2 := (f (conv_mylist_listm (phi5f5t n1 n2))).
Definition phi5f4tft n1 n2 := (phi4f4t n1 n2) ++ [msg (vtrm (sk 2) n2 9 10 (pi2 (x2ft n2)) 32)].
Definition x6f4tft n1 n2 := (f (conv_mylist_listm (phi5f4tft n1 n2))).
(*Definition phi3fttft  n2 := (phi2ftt n2) ++ [msg  ((bsign (sk 3)  (pi1 (pi2 (pi1 (x3ftt n2 ))))),  (bsign (sk 3)  (pi1 (pi2 (pi2 (x3ftt n2 ))))))].

Definition x4fttft n2 := (f (conv_mylist_listm (phi3fttft n2))). *)
Definition phi5ftf4t n1 n2:= (phi4ftf3t n1 n2) ++ [msg (vtrm (sk 1) n1 13 14 (pi1 (x3ftft n1 n2)) 33)].
Definition x6ftf4t n1 n2 := (f (conv_mylist_listm (phi5ftf4t n1 n2))).
Definition phi5ftf3tft n1 n2:= (phi4ftf3t n1 n2) ++ [msg (vtrm (sk 2) n2 9 10 (pi2 (x4ftftt n1 n2)) 34)].
Definition x6ftf3tft n1 n2 := (f (conv_mylist_listm (phi5ftf3tft n1 n2))).
(**********************************************************************)
Definition phi5ftftf3t n1 n2:= (phi4ftftf2t n1 n2) ++ [msg (vtrm (sk 1) n1 23 24 (pi1 (x4fttt n1 n2)) 31)].
Definition x6ftftf3t n1 n2 := (f (conv_mylist_listm (phi5ftftf3t n1 n2))).

Definition phi5ftftf2tft n1 n2:= (phi4ftftf2t n1 n2) ++ [msg (vtrm (sk 2) n2 9 10 (pi2 (x2ft n2)) 32)].
Definition x6ftftf2tft n1 n2 := (f (conv_mylist_listm (phi5ftftf2tft n1 n2))).

(** voting terms *)


 
Definition voter1 x1 n1 n2 r1 x2 r2 := (ifm (eqm (to x1) (V 1)) (vtrm (sk 1) n1 n2 r1 (pi1 (x2)) r2) O).
Definition voter2 x1 n1 n2 r1 x2 r2 := (ifm (eqm (to x1) (V 2)) (vtrm (sk 2) n1 n2 r1 (pi2 (x2)) r2) O).
(** vote 2 *)

Definition q111v2 n1 n2 := (ifm (eqm (to (x54t n1 n2)) (V 1)) (voter2 (x65t n1 n2) n2 19 20 (x4ttt n1 n2) 37)
                                  (ifm (eqm (to (x54t n1 n2)) (V 2)) (voter1 (x64tft n1 n2) n1 7 8 (x2t n1) 38) O)).
 
 (*************************************************)                       

  
Definition q121v2 n1 n2 := (ifm (eqm (to (x5tf3t n1 n2)) (V 1)) (voter2 (x6tf4t n1 n2) n2 11 12 (x4tftt n1 n2) 39)  
                                  (ifm (eqm (to (x5tf3t n1 n2)) (V 2)) (voter1 (x6tf3tft n1 n2) n1 7 8 (x3tft n1 n2) 40) O)).


  
  
Definition q122v2 n1 n2 := (ifm (eqm (to (x5tftft n1 n2)) (V 1)) (voter2 (x6tftf3t n1 n2) n2 11 12 (x3tft n1 n2) 41)  
                                  (ifm (eqm (to (x5tftft n1 n2)) (V 2)) (voter1 (x6tftfttft n1 n2) n1 7 8 (x4tftft n1 n2) 42) O)).



  
Definition q211v2 n1 n2 := (ifm (eqm (to (x5f4t n1 n2)) (V 1))   (voter2 (x6f5t n1 n2) n2 9 10 (x2ft n2) 43)  
                                  (ifm (eqm (to (x5f4t n1 n2)) (V 2)) (voter1 (x6f4tft n1 n2) n1 23 24 (x4fttt n1 n2) 44) O)).



(***************************************************)

  

Definition q221v2 n1 n2:=  (ifm (eqm (to (x5ftf3t n1 n2)) (V 1)) (voter2 (x6ftf4t n1 n2) n2 9 10 (x4ftftt n1 n2) 45) 
                                  (ifm (eqm (to (x5ftf3t n1 n2)) (V 2)) (voter1 (x6ftf3tft n1 n2) n1 13 14 (x3ftft n1 n2) 46) O)).


  
  
Definition q222v2 n1 n2 :=  (ifm (eqm (to (x5ftftf2t n1 n2)) (V 1)) (voter2 (x6ftftf3t n1 n2) n2 9 10 (x3ftft n1 n2) 47)  
                                  (ifm (eqm (to (x5ftftf2t n1 n2)) (V 2)) (voter1 (x6ftftf2tft n1 n2) n1 13 14 (x4ftftft n1 n2) 48) O)).




(*****************************************************************************************)
 
Definition qs'111 n1 n2 := (ifm  (eqm (to (x4ttt n1 n2)) (V 2))& (bacc (pk 3) (b n2 19) (r 20) (pi2 (x4ttt n1 n2))) (q111v2 n1 n2)
                                     O).
 
 (*************************************************)                       

  
Definition qs'121 n1 n2 := (ifm (eqm (to (x4tftt n1 n2)) (V 2 ))& (bacc (pk 3) (b n2 11) (r 12) (pi2 (x4tftt n1 n2))) (q121v2 n1 n2)
                         O).

Definition qs'122 n1 n2 := (ifm (eqm (to (x4tftft n1 n2)) (V 1 ))& (bacc (pk 3) (b n1 7) (r 8) (pi1 (x4tftft n1 n2))) (q122v2 n1 n2)
                         O).
 
 
Definition qs'211 n1 n2 :=  (ifm (eqm (to (x4fttt n1 n2)) (V 1 ))& (bacc (pk 3) (b n1 23) (r 24) (pi1 (x4fttt n1 n2))) (q211v2 n1 n2)
                          O).



(***************************************************)

Definition qs'221 n1 n2:=   (ifm (eqm (to (x4ftftt n1 n2)) (V 2 ))& (bacc (pk 3) (b n2 9) (r 10) (pi2 (x4ftftt n1 n2))) (q221v2 n1 n2)
                           O).
Definition qs'222 n1 n2 :=  (ifm (eqm (to (x4ftftft n1 n2)) (V 1 ))& (bacc (pk 3) (b n1 13) (r 14) (pi1 (x4ftftft n1 n2))) (q222v2 n1 n2) O).


 
(*****************************************)
  
Definition q11_s'' n1 n2 :=  (ifm  (eqm (to (x3tt n1 )) (V 2)) (qs'111 n1 n2)
                                      O).
 
Definition q12_s'' n1 n2 := (ifm (eqm (to (x3tft n1 n2)) (V 1))& (bacc (pk 3) (b n1 7) (r 8) (pi2 (x3tft n1 n2))) (qs'121 n1 n2)
                                    (ifm (eqm (to (x3tft n1 n2)) (V 2))& (bacc (pk 3) (b n2 11) (r 12) (pi2 (x3tft n1 n2))) (qs'122 n1 n2)
                                                 O)).
 

Definition q21_s'' n1 n2 := (ifm  (eqm (to (x3ftt n2)) (V 1))  (qs'211 n1 n2)
                                   O).

Definition q22_s'' n1 n2  := (ifm (eqm (to (x3ftft n1 n2)) (V 1))& (bacc (pk 3) (b n1 13) (r 14) (pi1 (x3ftft n1 n2))) (qs'221 n1 n2)
                                    (ifm (eqm (to (x3ftft n1 n2)) (V 2))& (bacc (pk 3) (b n2 9) (r 10) (pi2 (x3ftft n1 n2))) (qs'222 n1 n2)
                                                   O)).
 
(********************************************************************************************)

Definition q1_ss'' n1 n2 := (ifm (eqm (to (x2t n1 )) (V 1))& (bacc (pk 3) (b n1 7) (r 8) (pi1 (x2t n1 )))  (q11_s'' n1 n2)
			           (ifm (eqm (to (x2t n1 )) (V 2))  (q12_s'' n1 n2)
                                                  O)).
 
Definition q2_ss'' n1 n2 :=  (ifm (eqm (to (x2ft n2)) (V 2))& (bacc (pk 3) (b n2 9) (r 10) (pi2 (x2ft n2)))  (q21_s'' n1 n2)
			           (ifm (eqm (to (x2ft n2)) (V 1))  (q22_s'' n1 n2)
                                                   O)).
 


Definition t5 n1 n2 :=  (ifm (eqm (to x1) (V 1)) (q1_ss'' n1 n2)
		    	           (ifm (eqm (to x1) (V 2))  (q2_ss'' n1 n2)
                                                   O )).

Definition phi6 n1 n2 := (phi5 n1 n2) ++ [msg (t5 n1 n2)] .











