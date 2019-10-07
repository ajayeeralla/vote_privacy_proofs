   Load "phase22".
 
(** some tactics *)

 
(*******************************************)
(** ** Phase-II : Voting Phase *)
 
(** 
- (V) -> C : sign( sk (A) , commit(v, r)) 

 *)
(** frame 6***)
  (** * Frame [phi6] *)
   
  Definition phi66t n1 n2 := (phi55t n1 n2) ++ [msg (vtrm (sk 2) n2 19 20 (pi2 (x4ttt n1 n2)) 37)].
  
Definition x76t n1 n2 := (f (conv_mylist_listm (phi66t n1 n2))).
 
 
  (*****************************************************************************)

Definition phi64tftt n1 n2 := (phi54tft n1 n2) ++ [msg (vtrm (sk 1) n1 7 8 (pi1 (x2t n1)) 38) ].
Definition x74tftt n1 n2 := (f (conv_mylist_listm (phi64tftt n1 n2))). 
(*
Definition phi3ttft n1  := (phi2tt n1) ++ [msg  ((bsign (sk 3)  (pi1 (pi2 (pi1  (x3tt n1 ))))),  (bsign (sk 3)  (pi1 (pi2 (pi2  (x3tt n1 ))))))].
Definition x4ttft n1 := (f (conv_mylist_listm (phi3ttft n1))).
*)
Definition phi6tf5t n1 n2 := (phi5tf4t n1 n2) ++ [msg (vtrm (sk 2) n2 11 12 (pi2 (x4tftt n1 n2)) 39)].
Definition x7tf5t n1 n2 := (f (conv_mylist_listm (phi6tf5t n1 n2))).

Definition phi6tf3tftt n1 n2 := (phi5tf3tft n1 n2) ++ [msg (vtrm (sk 1) n1 7 8 (pi1 (x3tft n1 n2)) 40)].
Definition x7tf3tftt n1 n2 := (f (conv_mylist_listm (phi6tf3tftt n1 n2))).
(**********************************************************************************)
 
Definition phi6tftf4t n1 n2 := (phi5tftf3t n1 n2) ++ [msg (vtrm (sk 2)  n2 11 12 (pi2 (x3tft n1 n2)) 41)].
Definition x7tftf4t n1 n2 := (f (conv_mylist_listm (phi6tftf4t n1 n2))).

Definition phi6tftfttftt n1 n2 := (phi5tftfttft n1 n2) ++ [msg (vtrm (sk 1) n1 7 8 (pi1 (x4tftft n1 n2)) 42)].
Definition x7tftfttftt n1 n2 := (f (conv_mylist_listm (phi6tftfttftt n1 n2))).
(*
Definition phi3tftfft n1 n2 := (phi2tft n1 n2) ++ [msg  ((bsign (sk 3)  (pi1 (pi2 (pi1 (x3tft n1 n2))))),  (bsign (sk 3)  (pi1 (pi2 (pi2 (x3tft n1 n2))))))].

Definition x4tftfft n1 n2 := (f (conv_mylist_listm (phi3tftfft n1 n2))).
 *)
(*
Definition phi3tfftt n1  := (phi2tfft n1) ++ [msg ok].
Definition x4tfftt n1  := (f (conv_mylist_listm (phi3tfftt n1))).

Definition phi3tfftft n1 n2 := (phi2tfft n1) ++ [msg ((pk 2), ( (e (b n2 21) 22),  (sign (sk 2) (e (b n2 21) 22))))].
Definition x4tfftft n1 n2 := (f (conv_mylist_listm (phi3tfftft n1 n2))). *)
Definition phi6f6t n1 n2 := (phi5f5t n1 n2) ++ [msg (vtrm (sk 2) n2 9 10 (pi2 (x2ft n2)) 43)].
Definition x7f6t n1 n2 := (f (conv_mylist_listm (phi6f6t n1 n2))).
Definition phi6f4tftt n1 n2 := (phi5f4tft n1 n2) ++ [msg (vtrm (sk 1) n1 23 24 (pi1 (x4fttt n1 n2)) 44)].
Definition x7f4tftt n1 n2 := (f (conv_mylist_listm (phi6f4tftt n1 n2))).
(*Definition phi3fttft  n2 := (phi2ftt n2) ++ [msg  ((bsign (sk 3)  (pi1 (pi2 (pi1 (x3ftt n2 ))))),  (bsign (sk 3)  (pi1 (pi2 (pi2 (x3ftt n2 ))))))].

Definition x4fttft n2 := (f (conv_mylist_listm (phi3fttft n2))). *)

Definition phi6ftf5t n1 n2:= (phi5ftf4t n1 n2) ++ [msg (vtrm (sk 2) n2 9 10 (pi2 (x4ftftt n1 n2)) 34)].
Definition x7ftf5t n1 n2 := (f (conv_mylist_listm (phi6ftf5t n1 n2))).
Definition phi6ftf3tftt n1 n2:= (phi5ftf3tft n1 n2) ++ [msg (vtrm (sk 1) n1 13 14 (pi1 (x3ftft n1 n2)) 33)] .
Definition x7ftf3tftt n1 n2 := (f (conv_mylist_listm (phi6ftf3tftt n1 n2))).
(**********************************************************************)
Definition phi6ftftf4t n1 n2:= (phi5ftftf3t n1 n2) ++ [msg (vtrm (sk 2) n2 9 10 (pi2 (x2ft n2)) 32)] .
Definition x7ftftf4t n1 n2 := (f (conv_mylist_listm (phi6ftftf4t n1 n2))).

Definition phi6ftftf2tftt n1 n2:= (phi5ftftf2tft n1 n2) ++ [msg (vtrm (sk 1) n1 23 24 (pi1 (x4fttt n1 n2)) 31)].
Definition x7ftftf2tftt n1 n2 := (f (conv_mylist_listm (phi6ftftf2tftt n1 n2))).

(** mixnetops *)

Definition mchecks (x1: message) := (eqm (to x1) (pk 5)) & (ver (pk 1)  (TWO, (pi1 (pi1 x1))) (pi2 (pi1 x1))) & (ver (pk 2)  (TWO, (pi1 (pi2 x1))) (pi2 (pi2 x1))).
 
Definition mixnet (x1:message) :=  (ifm (mchecks (x1)) (shuf (dec (pi1 (pi1 x1)) (sk 5)) (dec (pi1 (pi2 x1)) (sk 5)))  O).

Definition mnetop n x1 x2 := (ifm (eqm (to x1) (V n)) (mixnet x2) O).
 (*
Definition voter1 x1 n1 n2 r1 x2 r2 := (ifm (eqm (to x1) (V 1)) (vtrm (sk 1) n1 n2 r1 (pi1 (x2)) r2) O).
Definition voter2 x1 n1 n2 r1 x2 r2 := (ifm (eqm (to x1) (V 2)) (vtrm (sk 2) n1 n2 r1 (pi2 (x2)) r2) O).
(** vote 2 *)
  *)

Definition q111m n1 n2 := (ifm (eqm (to (x54t n1 n2)) (V 1)) (mnetop 2 (x65t n1 n2) (x76t n1 n2))
                                  (ifm (eqm (to (x54t n1 n2)) (V 2)) (mnetop 1 (x64tft n1 n2) (x74tftt n1 n2)) O)).
 
 (*************************************************)                       

  
Definition q121m n1 n2 := (ifm (eqm (to (x5tf3t n1 n2)) (V 1)) (mnetop 2 (x6tf4t n1 n2) (x7tf5t n1 n2))
                                  (ifm (eqm (to (x5tf3t n1 n2)) (V 2)) (mnetop 1 (x6tf3tft n1 n2) (x7tf3tftt n1 n2)) O)).


   
  
Definition q122m n1 n2 := (ifm (eqm (to (x5tftft n1 n2)) (V 1)) (mnetop 2 (x6tftf3t n1 n2) (x7tftf4t n1 n2))  
                                  (ifm (eqm (to (x5tftft n1 n2)) (V 2)) (mnetop 1 (x6tftfttft n1 n2) (x7tftfttftt n1 n2)) O)).



  
Definition q211m n1 n2 := (ifm (eqm (to (x5f4t n1 n2)) (V 1))   (mnetop 2 (x6f5t n1 n2) (x7f6t n1 n2))  
                                  (ifm (eqm (to (x5f4t n1 n2)) (V 2)) (mnetop 1 (x6f4tft n1 n2) (x7f4tftt n1 n2)) O)).



(***************************************************)

  

Definition q221m n1 n2:=  (ifm (eqm (to (x5ftf3t n1 n2)) (V 1)) (mnetop 2 (x6ftf4t n1 n2) (x7ftf5t n1 n2))
                                  (ifm (eqm (to (x5ftf3t n1 n2)) (V 2)) (mnetop 1 (x6ftf3tft n1 n2) (x7ftf3tftt n1 n2)) O)).


  
  
Definition q222m n1 n2 :=  (ifm (eqm (to (x5ftftf2t n1 n2)) (V 1)) (mnetop 2 (x6ftftf3t n1 n2) (x7ftftf4t n1 n2))  
                                  (ifm (eqm (to (x5ftftf2t n1 n2)) (V 2)) (mnetop 1 (x6ftftf2tft n1 n2) (x7ftftf2tftt n1 n2)) O)).




(*****************************************************************************************)
 
Definition qs''111 n1 n2 := (ifm  (eqm (to (x4ttt n1 n2)) (V 2))& (bacc (pk 3) (b n2 19) (r 20) (pi2 (x4ttt n1 n2))) (q111m n1 n2)
                                     O).
 
 (*************************************************)                       

  
Definition qs''121 n1 n2 := (ifm (eqm (to (x4tftt n1 n2)) (V 2 ))& (bacc (pk 3) (b n2 11) (r 12) (pi2 (x4tftt n1 n2))) (q121m n1 n2)
                         O).

Definition qs''122 n1 n2 := (ifm (eqm (to (x4tftft n1 n2)) (V 1 ))& (bacc (pk 3) (b n1 7) (r 8) (pi1 (x4tftft n1 n2))) (q122m n1 n2)
                         O).
 
 
Definition qs''211 n1 n2 :=  (ifm (eqm (to (x4fttt n1 n2)) (V 1 ))& (bacc (pk 3) (b n1 23) (r 24) (pi1 (x4fttt n1 n2))) (q211m n1 n2)
                          O).



(***************************************************)

Definition qs''221 n1 n2:=   (ifm (eqm (to (x4ftftt n1 n2)) (V 2 ))& (bacc (pk 3) (b n2 9) (r 10) (pi2 (x4ftftt n1 n2))) (q221m n1 n2)
                           O).
Definition qs''222 n1 n2 :=  (ifm (eqm (to (x4ftftft n1 n2)) (V 1 ))& (bacc (pk 3) (b n1 13) (r 14) (pi1 (x4ftftft n1 n2))) (q222m n1 n2) O).


 
(*****************************************)
  
Definition q11_s''' n1 n2 :=  (ifm  (eqm (to (x3tt n1 )) (V 2)) (qs''111 n1 n2)
                                      O).
 
Definition q12_s''' n1 n2 := (ifm (eqm (to (x3tft n1 n2)) (V 1))& (bacc (pk 3) (b n1 7) (r 8) (pi2 (x3tft n1 n2))) (qs''121 n1 n2)
                                    (ifm (eqm (to (x3tft n1 n2)) (V 2))& (bacc (pk 3) (b n2 11) (r 12) (pi2 (x3tft n1 n2))) (qs''122 n1 n2)
                                                 O)).
 

Definition q21_s''' n1 n2 := (ifm  (eqm (to (x3ftt n2)) (V 1))  (qs''211 n1 n2)
                                   O).

Definition q22_s''' n1 n2  := (ifm (eqm (to (x3ftft n1 n2)) (V 1))& (bacc (pk 3) (b n1 13) (r 14) (pi1 (x3ftft n1 n2))) (qs''221 n1 n2)
                                    (ifm (eqm (to (x3ftft n1 n2)) (V 2))& (bacc (pk 3) (b n2 9) (r 10) (pi2 (x3ftft n1 n2))) (qs''222 n1 n2)
                                                   O)).
 
(********************************************************************************************)

Definition q1_ss''' n1 n2 := (ifm (eqm (to (x2t n1 )) (V 1))& (bacc (pk 3) (b n1 7) (r 8) (pi1 (x2t n1 )))  (q11_s''' n1 n2)
			           (ifm (eqm (to (x2t n1 )) (V 2))  (q12_s''' n1 n2)
                                                  O)).
 
Definition q2_ss''' n1 n2 :=  (ifm (eqm (to (x2ft n2)) (V 2))& (bacc (pk 3) (b n2 9) (r 10) (pi2 (x2ft n2)))  (q21_s''' n1 n2)
			           (ifm (eqm (to (x2ft n2)) (V 1))  (q22_s''' n1 n2)
                                                   O)).
 


Definition t6 n1 n2 :=  (ifm (eqm (to x1) (V 1)) (q1_ss''' n1 n2)
		    	           (ifm (eqm (to x1) (V 2))  (q2_ss''' n1 n2)
                                                   O )).

Definition phi7 n1 n2 := (phi6 n1 n2) ++ [msg (t6 n1 n2)] .











