Load "phase23".
 
(** some tactics *)

 
(*******************************************)
(** ** Phase-II : Voting Phase *)
 
(** 
- (V) -> C : sign( sk (A) , commit(v, r)) 

 *)
(** frame 6***)
  (** * Frame [phi6] *)

Definition shuftrm (x1:message) :=  (shuf (dec (pi1 (pi1 x1)) (sk 5)) (dec (pi1 (pi2 x1)) (sk 5))).
   
Definition phi77t n1 n2 := (phi66t n1 n2) ++ [msg  (shuf (unblind (commit (v (N 0)) (rr (N 7))) (pi1 (k (N 3))) (rr (N 8)) (pi1 (x2t 0)))
                                                         (unblind (b 1 19) (pk 3) (r 20) (pi2 (x4ttt 0 1)))) ].
  
Definition x87t n1 n2 := (f (conv_mylist_listm (phi77t n1 n2))).

 
  (*****************************************************************************)
 
Definition phi74tf3t n1 n2 := (phi64tftt n1 n2) ++ [msg (shuftrm (x74tftt n1 n2)) ].
Definition x84tf3t n1 n2 := (f (conv_mylist_listm (phi74tf3t n1 n2))). 
(*
Definition phi3ttft n1  := (phi2tt n1) ++ [msg  ((bsign (sk 3)  (pi1 (pi2 (pi1  (x3tt n1 ))))),  (bsign (sk 3)  (pi1 (pi2 (pi2  (x3tt n1 ))))))].
Definition x4ttft n1 := (f (conv_mylist_listm (phi3ttft n1))).
*)
Definition phi7tf6t n1 n2 := (phi6tf5t n1 n2) ++ [msg (shuftrm (x7tf5t n1 n2) ) ].
Definition x8tf6t n1 n2 := (f (conv_mylist_listm (phi7tf6t n1 n2))).

Definition phi7tf3tf3t n1 n2 := (phi6tf3tftt n1 n2) ++ [msg (shuftrm (x7tf3tftt n1 n2)) ].
Definition x8tf3tf3t n1 n2 := (f (conv_mylist_listm (phi7tf3tf3t n1 n2))).
(**********************************************************************************)
 
Definition phi7tftf5t n1 n2 := (phi6tftf4t n1 n2) ++ [msg (shuftrm (x7tftf4t n1 n2) ) ].
Definition x8tftf5t n1 n2 := (f (conv_mylist_listm (phi7tftf5t n1 n2))).

Definition phi7tftfttf3t n1 n2 := (phi6tftfttftt n1 n2) ++ [msg (shuftrm (x7tftfttftt n1 n2) ) ].
Definition x8tftfttf3t n1 n2 := (f (conv_mylist_listm (phi7tftfttf3t n1 n2))).
(*
Definition phi3tftfft n1 n2 := (phi2tft n1 n2) ++ [msg  ((bsign (sk 3)  (pi1 (pi2 (pi1 (x3tft n1 n2))))),  (bsign (sk 3)  (pi1 (pi2 (pi2 (x3tft n1 n2))))))].

Definition x4tftfft n1 n2 := (f (conv_mylist_listm (phi3tftfft n1 n2))).
 *)
(*
Definition phi3tfftt n1  := (phi2tfft n1) ++ [msg ok].
Definition x4tfftt n1  := (f (conv_mylist_listm (phi3tfftt n1))).

Definition phi3tfftft n1 n2 := (phi2tfft n1) ++ [msg ((pk 2), ( (e (b n2 21) 22),  (sign (sk 2) (e (b n2 21) 22))))].
Definition x4tfftft n1 n2 := (f (conv_mylist_listm (phi3tfftft n1 n2))). *)
Definition phi7f7t n1 n2 := (phi6f6t n1 n2) ++ [msg (shuftrm (x7f6t n1 n2) ) ].
Definition x8f7t n1 n2 := (f (conv_mylist_listm (phi7f7t n1 n2))).

Definition phi7f4tf3t n1 n2 := (phi6f4tftt n1 n2) ++ [msg (shuftrm (x7f4tftt n1 n2) ) ].
Definition x8f4tf3t n1 n2 := (f (conv_mylist_listm (phi7f4tf3t n1 n2))).
(*Definition phi3fttft  n2 := (phi2ftt n2) ++ [msg  ((bsign (sk 3)  (pi1 (pi2 (pi1 (x3ftt n2 ))))),  (bsign (sk 3)  (pi1 (pi2 (pi2 (x3ftt n2 ))))))].

Definition x4fttft n2 := (f (conv_mylist_listm (phi3fttft n2))). *)

Definition phi7ftf6t n1 n2:= (phi6ftf5t n1 n2) ++ [msg (shuftrm (x7ftf5t n1 n2) ) ].
Definition x8ftf6t n1 n2 := (f (conv_mylist_listm (phi7ftf6t n1 n2))).
Definition phi7ftf3tf3t n1 n2:= (phi6ftf3tftt n1 n2) ++ [msg (shuftrm (x7ftf3tftt n1 n2) ) ] .
Definition x8ftf3tf3t n1 n2 := (f (conv_mylist_listm (phi7ftf3tf3t n1 n2))).
(**********************************************************************)
Definition phi7ftftf5t n1 n2:= (phi6ftftf4t n1 n2) ++ [msg (shuftrm (x7ftftf4t n1 n2) ) ] .
Definition x8ftftf5t n1 n2 := (f (conv_mylist_listm (phi7ftftf5t n1 n2))).

Definition phi7ftftf2tf3t n1 n2:= (phi6ftftf2tftt n1 n2) ++ [msg (shuftrm (x7ftftf2tftt n1 n2) ) ].
Definition x8ftftf2tf3t n1 n2 := (f (conv_mylist_listm (phi7ftftf2tf3t n1 n2))).

(** mixnetops *)
 
Definition revtrm1   n r2 := ((enc (r n) (pk 5) (r r2)), (sign (sk 1)  (THREE, (enc (r n) (pk 5) (r r2))))).
Definition revtrm2   n r2 := ((enc (r n) (pk 5) (r r2)), (sign (sk 2)  (THREE, (enc (r n) (pk 5) (r r2))))).

 Definition rev x1 n1 r1 n2 r2 := (ifm (eqm (to x1) (V 1)) (revtrm1 n1 r1) (ifm (eqm (to x1) (V 2)) (revtrm2 n2 r2)  O)).
 

 
Definition mixnet' x1 x2 n1 r1 n2 r2 :=  (ifm (mchecks (x1)) (rev x2 n1 r1 n2 r2)  O).

Definition mnetop' n x1 x2 x3 n1 r1 n2 r2 := (ifm (eqm (to x1) (V n)) (mixnet' x2 x3 n1 r1 n2 r2) O).
 (*
Definition voter1 x1 n1 n2 r1 x2 r2 := (ifm (eqm (to x1) (V 1)) (vtrm (sk 1) n1 n2 r1 (pi1 (x2)) r2) O).
Definition voter2 x1 n1 n2 r1 x2 r2 := (ifm (eqm (to x1) (V 2)) (vtrm (sk 2) n1 n2 r1 (pi2 (x2)) r2) O).
(** vote 2 *)
  *)

Definition q111r1 n1 n2 := (ifm (eqm (to (x54t n1 n2)) (V 1)) (mnetop' 2 (x65t n1 n2) (x76t n1 n2) (x87t n1 n2) 7 51 19 52) 
                                  (ifm (eqm (to (x54t n1 n2)) (V 2)) (mnetop' 1 (x64tft n1 n2) (x74tftt n1 n2) (x84tf3t n1 n2) 7 53 19 54) O)).
 
 (*************************************************)                       

  
Definition q121r1 n1 n2 := (ifm (eqm (to (x5tf3t n1 n2)) (V 1)) (mnetop' 2 (x6tf4t n1 n2) (x7tf5t n1 n2) (x8tf6t n1 n2) 7 55 11 56)
                                  (ifm (eqm (to (x5tf3t n1 n2)) (V 2)) (mnetop' 1 (x6tf3tft n1 n2) (x7tf3tftt n1 n2) (x8tf3tf3t n1 n2) 7 57 11 58)  O)).


   
  
Definition q122r1 n1 n2 := (ifm (eqm (to (x5tftft n1 n2)) (V 1)) (mnetop' 2 (x6tftf3t n1 n2) (x7tftf4t n1 n2)  (x8tftf5t n1 n2) 7 59 11 60)
                                  (ifm (eqm (to (x5tftft n1 n2)) (V 2)) (mnetop' 1 (x6tftfttft n1 n2) (x7tftfttftt n1 n2) (x8tftfttf3t n1 n2) 7 61 11 62)  O)).



  
Definition q211r1 n1 n2 := (ifm (eqm (to (x5f4t n1 n2)) (V 1))   (mnetop' 2 (x6f5t n1 n2) (x7f6t n1 n2) (x8f7t n1 n2) 23 63 9 64)
                                  (ifm (eqm (to (x5f4t n1 n2)) (V 2)) (mnetop' 1 (x6f4tft n1 n2) (x7f4tftt n1 n2) (x8f4tf3t n1 n2) 23 65 9 66) O)).



(***************************************************)

  

Definition q221r1 n1 n2:=  (ifm (eqm (to (x5ftf3t n1 n2)) (V 1)) (mnetop' 2 (x6ftf4t n1 n2) (x7ftf5t n1 n2) (x8ftf6t n1 n2) 13 66 9 68)
                                  (ifm (eqm (to (x5ftf3t n1 n2)) (V 2)) (mnetop' 1 (x6ftf3tft n1 n2) (x7ftf3tftt n1 n2) (x8ftf3tf3t n1 n2) 13 69 9 70) O)).


  
  
Definition q222r1 n1 n2 :=  (ifm (eqm (to (x5ftftf2t n1 n2)) (V 1)) (mnetop' 2 (x6ftftf3t n1 n2) (x7ftftf4t n1 n2) (x8ftftf5t n1 n2) 13 71 9 72) 
                                  (ifm (eqm (to (x5ftftf2t n1 n2)) (V 2)) (mnetop' 1 (x6ftftf2tft n1 n2) (x7ftftf2tftt n1 n2) (x8ftftf2tf3t n1 n2) 13 73 9 74) O)).




(*****************************************************************************************)
 
Definition q111s n1 n2 := (ifm  (eqm (to (x4ttt n1 n2)) (V 2))& (bacc (pk 3) (b n2 19) (r 20) (pi2 (x4ttt n1 n2))) (q111r1 n1 n2)
                                     O).
 
 (*************************************************)                       

  
Definition q121s n1 n2 := (ifm (eqm (to (x4tftt n1 n2)) (V 2 ))& (bacc (pk 3) (b n2 11) (r 12) (pi2 (x4tftt n1 n2))) (q121r1 n1 n2)
                         O).

Definition q122s n1 n2 := (ifm (eqm (to (x4tftft n1 n2)) (V 1 ))& (bacc (pk 3) (b n1 7) (r 8) (pi1 (x4tftft n1 n2))) (q122r1 n1 n2)
                         O).
 
 
Definition q211s n1 n2 :=  (ifm (eqm (to (x4fttt n1 n2)) (V 1 ))& (bacc (pk 3) (b n1 23) (r 24) (pi1 (x4fttt n1 n2))) (q211r1 n1 n2)
                          O).



(***************************************************)

Definition q221s n1 n2:=   (ifm (eqm (to (x4ftftt n1 n2)) (V 2 ))& (bacc (pk 3) (b n2 9) (r 10) (pi2 (x4ftftt n1 n2))) (q221r1 n1 n2)
                           O).
Definition q222s n1 n2 :=  (ifm (eqm (to (x4ftftft n1 n2)) (V 1 ))& (bacc (pk 3) (b n1 13) (r 14) (pi1 (x4ftftft n1 n2))) (q222r1 n1 n2) O).


 
(*****************************************)
  
Definition q11_r1 n1 n2 :=  (ifm  (eqm (to (x3tt n1 )) (V 2)) (q111s n1 n2)
                                      O).
 
Definition q12_r1 n1 n2 := (ifm (eqm (to (x3tft n1 n2)) (V 1))& (bacc (pk 3) (b n1 7) (r 8) (pi2 (x3tft n1 n2))) (q121s n1 n2)
                                    (ifm (eqm (to (x3tft n1 n2)) (V 2))& (bacc (pk 3) (b n2 11) (r 12) (pi2 (x3tft n1 n2))) (q122s n1 n2)
                                                 O)).
 

Definition q21_r1 n1 n2 := (ifm  (eqm (to (x3ftt n2)) (V 1))  (q211s n1 n2)
                                   O).

Definition q22_r1 n1 n2  := (ifm (eqm (to (x3ftft n1 n2)) (V 1))& (bacc (pk 3) (b n1 13) (r 14) (pi1 (x3ftft n1 n2))) (q221s n1 n2)
                                    (ifm (eqm (to (x3ftft n1 n2)) (V 2))& (bacc (pk 3) (b n2 9) (r 10) (pi2 (x3ftft n1 n2))) (q222s n1 n2)
                                                   O)).
 
(********************************************************************************************)

Definition q1_r1 n1 n2 := (ifm (eqm (to (x2t n1 )) (V 1))& (bacc (pk 3) (b n1 7) (r 8) (pi1 (x2t n1 )))  (q11_r1 n1 n2)
			           (ifm (eqm (to (x2t n1 )) (V 2))  (q12_r1 n1 n2)
                                                  O)).
 
Definition q2_r1 n1 n2 :=  (ifm (eqm (to (x2ft n2)) (V 2))& (bacc (pk 3) (b n2 9) (r 10) (pi2 (x2ft n2)))  (q21_r1 n1 n2)
			           (ifm (eqm (to (x2ft n2)) (V 1))  (q22_r1 n1 n2)
                                                   O)).
 


Definition t7 n1 n2 :=  (ifm (eqm (to x1) (V 1)) (q1_r1 n1 n2)
		    	           (ifm (eqm (to x1) (V 2))  (q2_r1 n1 n2)
                                                   O )).

Definition phi8 n1 n2 := (phi7 n1 n2) ++ [msg (t7 n1 n2)] .











