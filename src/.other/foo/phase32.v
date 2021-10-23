Load "phase31".
 
(** some tactics *)

 
(*******************************************)
(** ** Phase-II : Voting Phase *)
 
(** 
- (V) -> C : sign( sk (A) , commit(v, r)) 

 *)
(** frame 6***)
  (** * Frame [phi6] *) 
 
(************************1******************************************) 
Definition phi88t n1 n2 := (phi77t n1 n2) ++ [msg (revtrm1 7 51) ].
  
Definition x98t n1 n2 := (f (conv_mylist_listm (phi88t n1 n2))).


Definition phi87tft n1 n2 := (phi77t n1 n2) ++ [msg (revtrm2 19 52) ].
  
Definition x987tft n1 n2 := (f (conv_mylist_listm (phi77t n1 n2))).

 
(*************************2****************************************************)
 
Definition phi84tf4t n1 n2 := (phi74tf3t n1 n2) ++ [msg (revtrm1 7 53) ].
Definition x94tf4t n1 n2 := (f (conv_mylist_listm (phi84tf4t n1 n2))).

Definition phi84tf3tft n1 n2 := (phi74tf3t n1 n2) ++ [msg (revtrm2 19 54)].
Definition x94tf3tft n1 n2 := (f (conv_mylist_listm (phi84tf3tft n1 n2))).  
(***************************3**************************************************)

Definition phi8tf7t n1 n2 := (phi7tf6t n1 n2) ++ [msg (revtrm1 7 55) ].
Definition x9tf7t n1 n2 := (f (conv_mylist_listm (phi8tf7t n1 n2))).

Definition phi8tf6tft n1 n2 := (phi7tf6t n1 n2) ++ [msg (revtrm2 11 56) ].
Definition x9tf6tft n1 n2 := (f (conv_mylist_listm (phi8tf6tft n1 n2))).

(*****************************4*************************************)

Definition phi8tf3tf4t n1 n2 := (phi7tf3tf3t n1 n2) ++ [msg (revtrm1 7 57) ].
Definition x9tf3tf4t n1 n2 := (f (conv_mylist_listm (phi8tf3tf4t n1 n2))).

Definition phi8tf3tf3tft n1 n2 := (phi7tf3tf3t n1 n2) ++ [msg (revtrm2 11 58) ].
Definition x9tf3tf3tft n1 n2 := (f (conv_mylist_listm (phi8tf3tf3tft n1 n2))).

(*****************************5*****************************************************)
 
Definition phi8tftf6t n1 n2 := (phi7tftf5t n1 n2) ++ [msg (revtrm1 7 59) ].
Definition x9tftf6t n1 n2 := (f (conv_mylist_listm (phi8tftf6t n1 n2))).

Definition phi8tftf5tft n1 n2 := (phi7tftf5t n1 n2) ++ [msg (revtrm2 11 60) ].
Definition x9tftf5tft n1 n2 := (f (conv_mylist_listm (phi8tftf5tft n1 n2))).

(*****************************6****************************************)
Definition phi8tftfttf4t n1 n2 := (phi7tftfttf3t n1 n2) ++ [msg (revtrm1 7 61) ].
Definition x9tftfttf4t n1 n2 := (f (conv_mylist_listm (phi8tftfttf4t n1 n2))).

Definition phi8tftfttf3tft n1 n2 := (phi7tftfttf3t n1 n2) ++ [msg (revtrm2 11 62) ].
Definition x9tftfttf3tft n1 n2 := (f (conv_mylist_listm (phi8tftfttf3tft n1 n2))).

(******************************7***************************************)
Definition phi8f8t n1 n2 := (phi7f7t n1 n2) ++ [msg (revtrm1 23 63) ].
Definition x9f8t n1 n2 := (f (conv_mylist_listm (phi8f8t n1 n2))).

Definition phi8f7tft n1 n2 := (phi7f7t n1 n2) ++ [msg (revtrm2 9 64) ].
Definition x9f7tft n1 n2 := (f (conv_mylist_listm (phi8f7tft n1 n2))).

(*****************************8****************************************)

Definition phi8f4tf4t n1 n2 := (phi7f4tf3t n1 n2) ++ [msg (revtrm1 23 65) ].
Definition x9f4tf4t n1 n2 := (f (conv_mylist_listm (phi8f4tf4t n1 n2))).


Definition phi8f4tf3tft n1 n2 := (phi7f4tf3t n1 n2) ++ [msg (revtrm2 9 66) ].
Definition x9f4tf3tft n1 n2 := (f (conv_mylist_listm (phi8f4tf3tft n1 n2))).

(******************************9**************************************)

Definition phi8ftf7t n1 n2:= (phi7ftf6t n1 n2) ++ [msg (revtrm1 13 66)].
Definition x9ftf7t n1 n2 := (f (conv_mylist_listm (phi8ftf7t n1 n2))).

Definition phi8ftf6tft n1 n2:= (phi7ftf6t n1 n2) ++ [msg (revtrm2 9 68) ].
Definition x9ftf6tft n1 n2 := (f (conv_mylist_listm (phi8ftf6tft n1 n2))).

(******************************10*************************************)

Definition phi8ftf3tf4t n1 n2:= (phi7ftf3tf3t n1 n2) ++ [msg (revtrm1 13 69) ] .
Definition x9ftf3tf4t n1 n2 := (f (conv_mylist_listm (phi8ftf3tf4t n1 n2))).


Definition phi7ftf3tf3tft n1 n2:= (phi7ftf3tf3t n1 n2) ++ [msg (revtrm2 9 70) ] .
Definition x9ftf3tf3tft n1 n2 := (f (conv_mylist_listm (phi7ftf3tf3tft n1 n2))).
(*******************************11***************************************)
Definition phi8ftftf6t n1 n2:= (phi7ftftf5t n1 n2) ++ [msg (revtrm1 13 71) ] .
Definition x9ftftf6t n1 n2 := (f (conv_mylist_listm (phi8ftftf6t n1 n2))).
Definition phi8ftftf5tft n1 n2:= (phi7ftftf5t n1 n2) ++ [msg (revtrm2 9 72) ] .
Definition x9ftftf5tft n1 n2 := (f (conv_mylist_listm (phi8ftftf5tft n1 n2))).

(*********************************12**************************************)
Definition phi8ftftf2tf4t n1 n2:= (phi7ftftf2tf3t n1 n2) ++ [msg (revtrm1 13 73) ].
Definition x9ftftf2tf4t n1 n2 := (f (conv_mylist_listm (phi8ftftf2tf4t n1 n2))).

Definition phi8ftftf2tf3tft n1 n2:= (phi7ftftf2tf3t n1 n2) ++ [msg (revtrm2 9 74) ].
Definition x9ftftf2tf3tft n1 n2 := (f (conv_mylist_listm (phi8ftftf2tf3tft n1 n2))).


(**************************r2 reveals*******************************************)



Definition ifrevtrm2 x' n2 r2 := (ifm (eqm (to x') (V 2)) (revtrm2 n2 r2) O).

Definition ifrevtrm1 x n1 r1 := (ifm (eqm (to x) (V 1)) (revtrm1 n1 r1) O).


 Definition rev' x1 x2 x3 n1 r1 n2 r2 := (ifm (eqm (to x1) (V 1)) (ifrevtrm2 x2 n2 r2) (ifm (eqm (to x1) (V 2)) (ifrevtrm1 x3 n1 r1)  O)).


Definition mixnet'' x1 x2 x3 x4 n1 r1 n2 r2 :=  (ifm (mchecks (x1)) (rev' x2 x3 x4 n1 r1 n2 r2)  O).

Definition mnetop'' n x1 x2 x3 x4 x5 n1 r1 n2 r2 := (ifm (eqm (to x1) (V n)) (mixnet'' x2 x3 x4 x5 n1 r1 n2 r2) O).
 
Definition q111r2 n1 n2 := (ifm (eqm (to (x54t n1 n2)) (V 1)) (mnetop'' 2 (x65t n1 n2) (x76t n1 n2) (x87t n1 n2) (x98t n1 n2) (x987tft n1 n2) 7 51 19 52) 
                                  (ifm (eqm (to (x54t n1 n2)) (V 2)) (mnetop'' 1 (x64tft n1 n2) (x74tftt n1 n2) (x84tf3t n1 n2) (x94tf4t n1 n2) (x94tf3tft n1 n2) 7 53 19 54) O)).
 
 (*************************************************)                       

  
Definition q121r2 n1 n2 := (ifm (eqm (to (x5tf3t n1 n2)) (V 1)) (mnetop'' 2 (x6tf4t n1 n2) (x7tf5t n1 n2) (x8tf6t n1 n2) (x9tf7t n1 n2) (x9tf6tft n1 n2) 7 55 11 56)
                                  (ifm (eqm (to (x5tf3t n1 n2)) (V 2)) (mnetop'' 1 (x6tf3tft n1 n2) (x7tf3tftt n1 n2) (x8tf3tf3t n1 n2) (x9tf3tf4t n1 n2) (x9tf3tf3tft n1 n2) 7 57 11 58)  O)).


   
  
Definition q122r2 n1 n2 := (ifm (eqm (to (x5tftft n1 n2)) (V 1)) (mnetop'' 2 (x6tftf3t n1 n2) (x7tftf4t n1 n2)  (x8tftf5t n1 n2) (x9tftf6t n1 n2) (x9tftf5tft n1 n2) 7 59 11 60)
                                  (ifm (eqm (to (x5tftft n1 n2)) (V 2)) (mnetop'' 1 (x6tftfttft n1 n2) (x7tftfttftt n1 n2) (x8tftfttf3t n1 n2) (x9tftfttf4t n1 n2) (x9tftfttf3tft n1 n2) 7 61 11 62)  O)).



  
Definition q211r2 n1 n2 := (ifm (eqm (to (x5f4t n1 n2)) (V 1))   (mnetop'' 2 (x6f5t n1 n2) (x7f6t n1 n2) (x8f7t n1 n2) (x9f8t n1 n2)  (x9f7tft n1 n2) 23 63 9 64)
                                  (ifm (eqm (to (x5f4t n1 n2)) (V 2)) (mnetop'' 1 (x6f4tft n1 n2) (x7f4tftt n1 n2) (x8f4tf3t n1 n2) (x9f4tf4t n1 n2) (x9f4tf3tft n1 n2)24 65 9 66) O)).



(***************************************************)

  

Definition q221r2 n1 n2:=  (ifm (eqm (to (x5ftf3t n1 n2)) (V 1)) (mnetop'' 2 (x6ftf4t n1 n2) (x7ftf5t n1 n2) (x8ftf6t n1 n2) (x9ftf7t n1 n2) (x9ftf6tft n1 n2) 13 66 9 68)
                                  (ifm (eqm (to (x5ftf3t n1 n2)) (V 2)) (mnetop'' 1 (x6ftf3tft n1 n2) (x7ftf3tftt n1 n2) (x8ftf3tf3t n1 n2) (x9ftf3tf4t n1 n2) (x9ftf3tf3tft n1 n2) 13 69 9 70) O)).


  
  
Definition q222r2 n1 n2 :=  (ifm (eqm (to (x5ftftf2t n1 n2)) (V 1)) (mnetop'' 2 (x6ftftf3t n1 n2) (x7ftftf4t n1 n2) (x8ftftf5t n1 n2) (x9ftftf6t n1 n2) (x9ftftf5tft n1 n2) 13 71 9 72) 
                                  (ifm (eqm (to (x5ftftf2t n1 n2)) (V 2)) (mnetop'' 1 (x6ftftf2tft n1 n2) (x7ftftf2tftt n1 n2) (x8ftftf2tf3t n1 n2) (x9ftftf2tf4t n1 n2) (x9ftftf2tf3tft n1 n2) 13 73 9 74) O)).




(*****************************************************************************************)
 
Definition q111s' n1 n2 := (ifm  (eqm (to (x4ttt n1 n2)) (V 2))& (bacc (pk 3) (b n2 19) (r 20) (pi2 (x4ttt n1 n2))) (q111r2 n1 n2)
                                     O).
 
 (*************************************************)                       

  
Definition q121s' n1 n2 := (ifm (eqm (to (x4tftt n1 n2)) (V 2 ))& (bacc (pk 3) (b n2 11) (r 12) (pi2 (x4tftt n1 n2))) (q121r2 n1 n2)
                         O).

Definition q122s' n1 n2 := (ifm (eqm (to (x4tftft n1 n2)) (V 1 ))& (bacc (pk 3) (b n1 7) (r 8) (pi1 (x4tftft n1 n2))) (q122r2 n1 n2)
                         O).
 
 
Definition q211s' n1 n2 :=  (ifm (eqm (to (x4fttt n1 n2)) (V 1 ))& (bacc (pk 3) (b n1 23) (r 24) (pi1 (x4fttt n1 n2))) (q211r2 n1 n2)
                          O).



(***************************************************)

Definition q221s' n1 n2:=   (ifm (eqm (to (x4ftftt n1 n2)) (V 2 ))& (bacc (pk 3) (b n2 9) (r 10) (pi2 (x4ftftt n1 n2))) (q221r2 n1 n2)
                           O).
Definition q222s' n1 n2 :=  (ifm (eqm (to (x4ftftft n1 n2)) (V 1 ))& (bacc (pk 3) (b n1 13) (r 14) (pi1 (x4ftftft n1 n2))) (q222r2 n1 n2) O).


 
(*****************************************)
  
Definition q11_r2 n1 n2 :=  (ifm  (eqm (to (x3tt n1 )) (V 2)) (q111s' n1 n2)
                                      O).
 
Definition q12_r2 n1 n2 := (ifm (eqm (to (x3tft n1 n2)) (V 1))& (bacc (pk 3) (b n1 7) (r 8) (pi2 (x3tft n1 n2))) (q121s' n1 n2)
                                    (ifm (eqm (to (x3tft n1 n2)) (V 2))& (bacc (pk 3) (b n2 11) (r 12) (pi2 (x3tft n1 n2))) (q122s' n1 n2)
                                                 O)).
 

Definition q21_r2 n1 n2 := (ifm  (eqm (to (x3ftt n2)) (V 1))  (q211s' n1 n2)
                                   O).

Definition q22_r2 n1 n2  := (ifm (eqm (to (x3ftft n1 n2)) (V 1))& (bacc (pk 3) (b n1 13) (r 14) (pi1 (x3ftft n1 n2))) (q221s' n1 n2)
                                    (ifm (eqm (to (x3ftft n1 n2)) (V 2))& (bacc (pk 3) (b n2 9) (r 10) (pi2 (x3ftft n1 n2))) (q222s' n1 n2)
                                                   O)).
 
(********************************************************************************************)

Definition q1_r2 n1 n2 := (ifm (eqm (to (x2t n1 )) (V 1))& (bacc (pk 3) (b n1 7) (r 8) (pi1 (x2t n1 )))  (q11_r2 n1 n2)
			           (ifm (eqm (to (x2t n1 )) (V 2))  (q12_r2 n1 n2)
                                                  O)).
 
Definition q2_r2 n1 n2 :=  (ifm (eqm (to (x2ft n2)) (V 2))& (bacc (pk 3) (b n2 9) (r 10) (pi2 (x2ft n2)))  (q21_r2 n1 n2)
			           (ifm (eqm (to (x2ft n2)) (V 1))  (q22_r2 n1 n2)
                                                   O)).
 


Definition t8 n1 n2 :=  (ifm (eqm (to x1) (V 1)) (q1_r2 n1 n2)
		    	           (ifm (eqm (to x1) (V 2))  (q2_r2 n1 n2)
                                                   O )).

Definition phi9 n1 n2 := (phi8 n1 n2) ++ [msg (t8 n1 n2)] .











