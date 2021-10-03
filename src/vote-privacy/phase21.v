 Load "foo_prot2".
 
(** some tactics *)

 
(*******************************************)
(** ** Phase-II : Voting Phase *)
 
(** 
- (V) -> C : sign( sk (A) , commit(v, r)) 

 *)
(** frame 5***)
(** * Frame [phi4] *)
Definition mphi44t n1 n2 := (mphi3ttt n1 n2) ++ [msg ok].
Definition x54t n1 n2 := (f (conv_mylist_listm (mphi44t n1 n2))). 
(*
Definition phi3ttft n1  := (phi2tt n1) ++ [msg  ((bsign (sk 3)  (pi1 (pi2 (pi1  (x3tt n1 ))))),  (bsign (sk 3)  (pi1 (pi2 (pi2  (x3tt n1 ))))))].
Definition x4ttft n1 := (f (conv_mylist_listm (phi3ttft n1))).
*)
Definition phi4tf3t n1 n2 := (phi3tftt n1 n2) ++ [msg ok].
Definition x5tf3t n1 n2 := (f (conv_mylist_listm (phi4tf3t n1 n2))).

Definition phi4tftftt n1 n2 := (phi3tftft n1 n2) ++ [msg ok].
Definition x5tftft n1 n2 := (f (conv_mylist_listm (phi3tftft n1 n2))).
(*
Definition phi3tftfft n1 n2 := (phi2tft n1 n2) ++ [msg  ((bsign (sk 3)  (pi1 (pi2 (pi1 (x3tft n1 n2))))),  (bsign (sk 3)  (pi1 (pi2 (pi2 (x3tft n1 n2))))))].

Definition x4tftfft n1 n2 := (f (conv_mylist_listm (phi3tftfft n1 n2))).
 *)
(*
Definition phi3tfftt n1  := (phi2tfft n1) ++ [msg ok].
Definition x4tfftt n1  := (f (conv_mylist_listm (phi3tfftt n1))).

Definition phi3tfftft n1 n2 := (phi2tfft n1) ++ [msg ((pk 2), ( (e (b n2 21) 22),  (sign (sk 2) (e (b n2 21) 22))))].
Definition x4tfftft n1 n2 := (f (conv_mylist_listm (phi3tfftft n1 n2))). *)
Definition phi4f4t n1 n2 := (phi3fttt n1 n2) ++ [msg ok].

Definition x5f4t n1 n2 := (f (conv_mylist_listm (phi4f4t n1 n2))).
(*Definition phi3fttft  n2 := (phi2ftt n2) ++ [msg  ((bsign (sk 3)  (pi1 (pi2 (pi1 (x3ftt n2 ))))),  (bsign (sk 3)  (pi1 (pi2 (pi2 (x3ftt n2 ))))))].

Definition x4fttft n2 := (f (conv_mylist_listm (phi3fttft n2))). *)
Definition phi4ftf3t n1 n2:= (phi3ftftt n1 n2) ++ [msg ok].
Definition x5ftf3t n1 n2 := (f (conv_mylist_listm (phi4ftf3t n1 n2))).
Definition phi4ftftf2t n1 n2:= (phi3ftftft n1 n2) ++ [msg ok].
Definition x5ftftf2t n1 n2 := (f (conv_mylist_listm (phi4ftftf2t n1 n2))).

(** voting terms *)


Definition vtrm ssk n1 n2 r1 x r2 := ((enc (unblind (b n1 n2) (pk 3) (r r1) x) (pk 5) (r r2)), (sign ssk  (TWO, (enc (unblind (b n1 n2) (pk 3) (r r1) x) (pk 5) (r r2))))).

 
Definition q111v1 n1 n2 := (ifm (eqm (to (x54t n1 n2)) (V 1)) (vtrm (sk 1) n1 7 8 (pi1 (x2t n1)) 25)  
                                  (ifm (eqm (to (x54t n1 n2)) (V 2)) (vtrm (sk 2) n2 19 20 (pi2 (x4ttt n1 n2)) 26) O)).
 
 (*************************************************)                       

  
Definition q121v1 n1 n2 := (ifm (eqm (to (x5tf3t n1 n2)) (V 1)) (vtrm (sk 1) n1 7 8 (pi1 (x3tft n1 n2)) 27)  
                                  (ifm (eqm (to (x5tf3t n1 n2)) (V 2)) (vtrm (sk 2) n2 11 12 (pi2 (x4tftt n1 n2)) 28) O)).
 
Definition q122v1 n1 n2 := (ifm (eqm (to (x5tftft n1 n2)) (V 1)) (vtrm (sk 1) n1 7 8 (pi1 (x4tftft n1 n2)) 29)  
                                  (ifm (eqm (to (x5tftft n1 n2)) (V 2)) (vtrm (sk 2) n2 11 12 (pi2 (x3tft n1 n2)) 30) O)).
 
  
Definition q211v1 n1 n2 := (ifm (eqm (to (x5f4t n1 n2)) (V 1)) (vtrm (sk 1) n1 23 24 (pi1 (x4fttt n1 n2)) 31)  
                                  (ifm (eqm (to (x5f4t n1 n2)) (V 2)) (vtrm (sk 2) n2 9 10 (pi2 (x2ft n2)) 32) O)).



(***************************************************)

Definition q221v1 n1 n2:=  (ifm (eqm (to (x5ftf3t n1 n2)) (V 1)) (vtrm (sk 1) n1 13 14 (pi1 (x3ftft n1 n2)) 33)  
                                  (ifm (eqm (to (x5ftf3t n1 n2)) (V 2)) (vtrm (sk 2) n2 9 10 (pi2 (x4ftftt n1 n2)) 34) O)).

Definition q222v1 n1 n2 :=  (ifm (eqm (to (x5ftftf2t n1 n2)) (V 1)) (vtrm (sk 1) n1 13 14 (pi1 (x4ftftft n1 n2)) 35)  
                                  (ifm (eqm (to (x5ftftf2t n1 n2)) (V 2)) (vtrm (sk 2) n2 9 10 (pi2 (x3ftft n1 n2)) 36) O)).




(*****************************************************************************************)
 
Definition qs111 n1 n2 := (ifm  (eqm (to (x4ttt n1 n2)) (V 2))& (bacc (pk 3) (b n2 19) (r 20) (pi2 (x4ttt n1 n2))) (q111v1 n1 n2)
                                     O).
 
 (*************************************************)                       

  
Definition qs121 n1 n2 := (ifm (eqm (to (x4tftt n1 n2)) (V 2 ))& (bacc (pk 3) (b n2 11) (r 12) (pi2 (x4tftt n1 n2))) (q121v1 n1 n2)
                         O).

Definition qs122 n1 n2 := (ifm (eqm (to (x4tftft n1 n2)) (V 1 ))& (bacc (pk 3) (b n1 7) (r 8) (pi1 (x4tftft n1 n2))) (q122v1 n1 n2)
                         O).
 
 
Definition qs211 n1 n2 :=  (ifm (eqm (to (x4fttt n1 n2)) (V 1 ))& (bacc (pk 3) (b n1 23) (r 24) (pi1 (x4fttt n1 n2))) (q211v1 n1 n2)
                          O).



(***************************************************)

Definition qs221 n1 n2:=   (ifm (eqm (to (x4ftftt n1 n2)) (V 2 ))& (bacc (pk 3) (b n2 9) (r 10) (pi2 (x4ftftt n1 n2))) (q221v1 n1 n2)
                           O).
Definition qs222 n1 n2 :=  (ifm (eqm (to (x4ftftft n1 n2)) (V 1 ))& (bacc (pk 3) (b n1 13) (r 14) (pi1 (x4ftftft n1 n2))) (q222v1 n1 n2) O).


 
(*****************************************)
  
Definition q11_s' n1 n2 :=  (ifm  (eqm (to (x3tt n1 )) (V 2)) (qs111 n1 n2)
                                      O).
 
Definition q12_s' n1 n2 := (ifm (eqm (to (x3tft n1 n2)) (V 1))& (bacc (pk 3) (b n1 7) (r 8) (pi2 (x3tft n1 n2))) (qs121 n1 n2)
                                    (ifm (eqm (to (x3tft n1 n2)) (V 2))& (bacc (pk 3) (b n2 11) (r 12) (pi2 (x3tft n1 n2))) (qs122 n1 n2)
                                                 O)).
 

Definition q21_s' n1 n2 := (ifm  (eqm (to (x3ftt n2)) (V 1))  (qs211 n1 n2)
                                   O).

Definition q22_s' n1 n2  := (ifm (eqm (to (x3ftft n1 n2)) (V 1))& (bacc (pk 3) (b n1 13) (r 14) (pi1 (x3ftft n1 n2))) (qs221 n1 n2)
                                    (ifm (eqm (to (x3ftft n1 n2)) (V 2))& (bacc (pk 3) (b n2 9) (r 10) (pi2 (x3ftft n1 n2))) (qs222 n1 n2)
                                                   O)).
 
(********************************************************************************************)

Definition q1_ss' n1 n2 := (ifm (eqm (to (x2t n1 )) (V 1))& (bacc (pk 3) (b n1 7) (r 8) (pi1 (x2t n1 )))  (q11_s' n1 n2)
			           (ifm (eqm (to (x2t n1 )) (V 2))  (q12_s' n1 n2)
                                                  O)).
 
Definition q2_ss' n1 n2 :=  (ifm (eqm (to (x2ft n2)) (V 2))& (bacc (pk 3) (b n2 9) (r 10) (pi2 (x2ft n2)))  (q21_s' n1 n2)
			           (ifm (eqm (to (x2ft n2)) (V 1))  (q22_s' n1 n2)
                                                   O)).
 


Definition t4 n1 n2 :=  (ifm (eqm (to x1) (V 1)) (q1_ss' n1 n2)
		    	           (ifm (eqm (to x1) (V 2))  (q2_ss' n1 n2)
                                                   O )).

Definition phi5 n1 n2 := (phi4 n1 n2) ++ [msg (t4 n1 n2)] .


















