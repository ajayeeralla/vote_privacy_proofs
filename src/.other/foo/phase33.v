Load "phase32".
  
(** some tactics *)

 
(*******************************************)
(** ** Phase-II : Voting Phase *)
 
(** 
- (V) -> C : sign( sk (A) , commit(v, r)) 

 *)
(** frame 6***)
  (** * Frame [phi6] *) 
 
(************************1******************************************) 
Definition phi99t n1 n2 := (phi88t n1 n2) ++ [msg (revtrm2 19 52) ]. 
  
Definition x109t n1 n2 := (f (conv_mylist_listm (phi88t n1 n2))).


Definition phi97tftt n1 n2 := (phi87tft n1 n2) ++  [msg (revtrm1 7 51) ].
  
Definition x1087tftt n1 n2 := (f (conv_mylist_listm (phi97tftt n1 n2))).

 
(*************************2****************************************************)
 
Definition phi94tf4tt n1 n2 := (phi84tf4t n1 n2) ++ [msg (revtrm2 19 54)].
Definition x104tf4tt n1 n2 := (f (conv_mylist_listm (phi94tf4tt n1 n2))).

Definition phi94tf3tftt n1 n2 := (phi84tf3tft n1 n2) ++ [msg (revtrm1 7 53) ]. 
Definition x104tf3tftt n1 n2 := (f (conv_mylist_listm (phi94tf3tftt n1 n2))).  
(***************************3**************************************************)

Definition phi9tf7tt n1 n2 := (phi8tf7t n1 n2) ++  [msg (revtrm2 11 56) ].
Definition x10tf7tt n1 n2 := (f (conv_mylist_listm (phi9tf7tt n1 n2))).

Definition phi9tf6tftt n1 n2 := (phi8tf6tft n1 n2) ++ [msg (revtrm1 7 55) ].
Definition x10tf6tftt n1 n2 := (f (conv_mylist_listm (phi9tf6tftt n1 n2))).

(*****************************4*************************************)

Definition phi9tf3tf4tt n1 n2 := (phi8tf3tf4t n1 n2) ++ [msg (revtrm2 11 58) ].
Definition x10tf3tf4tt n1 n2 := (f (conv_mylist_listm (phi9tf3tf4tt n1 n2))).

Definition phi9tf3tf3tftt n1 n2 := (phi8tf3tf3tft n1 n2) ++ [msg (revtrm1 7 57) ]. 
Definition x10tf3tf3tftt n1 n2 := (f (conv_mylist_listm (phi9tf3tf3tftt n1 n2))).

(*****************************5*****************************************************)
 
Definition phi9tftf6tt n1 n2 := (phi8tftf6t n1 n2) ++ [msg (revtrm2 11 60) ].
Definition x10tftf6tt n1 n2 := (f (conv_mylist_listm (phi9tftf6tt n1 n2))).

Definition phi9tftf5tftt n1 n2 := (phi8tftf5tft n1 n2) ++ [msg (revtrm1 7 59) ]. 
Definition x10tftf5tftt n1 n2 := (f (conv_mylist_listm (phi9tftf5tftt n1 n2))).

(*****************************6****************************************)
Definition phi9tftfttf4tt n1 n2 := (phi8tftfttf4t n1 n2) ++ [msg (revtrm2 11 62) ]. 
Definition x10tftfttf4tt n1 n2 := (f (conv_mylist_listm (phi9tftfttf4tt n1 n2))).

Definition phi9tftfttf3tftt n1 n2 := (phi8tftfttf3tft n1 n2) ++ [msg (revtrm1 7 61) ].
Definition x10tftfttf3tftt n1 n2 := (f (conv_mylist_listm (phi9tftfttf3tftt n1 n2))).

(******************************7***************************************)
Definition phi9f8tt n1 n2 := (phi8f8t n1 n2) ++ [msg (revtrm2 9 64) ]. 
Definition x10f8tt n1 n2 := (f (conv_mylist_listm (phi9f8tt n1 n2))).

Definition phi9f7tftt n1 n2 := (phi8f7tft n1 n2) ++ [msg (revtrm1 23 63) ].
Definition x10f7tftt n1 n2 := (f (conv_mylist_listm (phi9f7tftt n1 n2))).

(*****************************8****************************************)

Definition phi9f4tf4tt n1 n2 := (phi8f4tf4t n1 n2) ++  [msg (revtrm2 9 66) ].
Definition x10f4tf4tt n1 n2 := (f (conv_mylist_listm (phi9f4tf4tt n1 n2))).


Definition phi9f4tf3tftt n1 n2 := (phi8f4tf3tft n1 n2) ++ [msg (revtrm1 23 65) ].
Definition x10f4tf3tftt n1 n2 := (f (conv_mylist_listm (phi9f4tf3tftt n1 n2))).

(******************************9**************************************)

Definition phi9ftf7tt n1 n2:= (phi8ftf7t n1 n2) ++ [msg (revtrm2 9 68) ].
Definition x10ftf7tt n1 n2 := (f (conv_mylist_listm (phi9ftf7tt n1 n2))).

Definition phi9ftf6tftt n1 n2:= (phi8ftf6tft n1 n2) ++ [msg (revtrm1 13 66)]. 
Definition x10ftf6tftt n1 n2 := (f (conv_mylist_listm (phi9ftf6tftt n1 n2))).

(******************************10*************************************)

Definition phi9ftf3tf4tt n1 n2:= (phi8ftf3tf4t n1 n2) ++  [msg (revtrm2 9 70) ] .
Definition x10ftf3tf4tt n1 n2 := (f (conv_mylist_listm (phi9ftf3tf4tt n1 n2))).


Definition phi7ftf3tf3tftt n1 n2:= (phi7ftf3tf3tft n1 n2) ++ [msg (revtrm1 13 69) ] .
Definition x10ftf3tf3tftt n1 n2 := (f (conv_mylist_listm (phi7ftf3tf3tftt n1 n2))).
(*******************************11***************************************)
Definition phi9ftftf6tt n1 n2:= (phi8ftftf6t n1 n2) ++ [msg (revtrm2 9 72) ] .
Definition x10ftftf6tt n1 n2 := (f (conv_mylist_listm (phi9ftftf6tt n1 n2))).
Definition phi9ftftf5tftt n1 n2:= (phi8ftftf5tft n1 n2) ++ [msg (revtrm1 13 71) ] . 
Definition x10ftftf5tftt n1 n2 := (f (conv_mylist_listm (phi9ftftf5tftt n1 n2))).

(*********************************12**************************************)
Definition phi9ftftf2tf4tt n1 n2:= (phi8ftftf2tf4t n1 n2) ++ [msg (revtrm2 9 74) ].
Definition x10ftftf2tf4tt n1 n2 := (f (conv_mylist_listm (phi9ftftf2tf4tt n1 n2))).

Definition phi9ftftf2tf3tftt n1 n2:= (phi8ftftf2tf3tft n1 n2) ++ [msg (revtrm1 13 73) ]. 
Definition x10ftftf2tf3tftt n1 n2 := (f (conv_mylist_listm (phi9ftftf2tf3tftt n1 n2))).


(**************************r2 reveals*******************************************)




Definition ifrevtrm2' x1 x2  := (ifm (eqm (to x1) (V 2)) (mixnet x2)  O).

Definition ifrevtrm1' x1 x2  := (ifm (eqm (to x1) (V 1)) (mixnet x2) O).


 Definition rev'' x1 x2 x3 x4 x5 := (ifm (eqm (to x1) (V 1)) (ifrevtrm2' x2 x4) (ifm (eqm (to x1) (V 2)) (ifrevtrm1' x3 x5) O)).


Definition mixnet''' x1 x2 x3 x4 x5 x6 :=  (ifm (mchecks (x1)) (rev'' x2 x3 x4 x5 x6)  O).

Definition mnetop''' n x1 x2 x3 x4 x5 x6 x7 := (ifm (eqm (to x1) (V n)) (mixnet''' x2 x3 x4 x5 x6 x7) O).
 
Definition q111m' n1 n2 := (ifm (eqm (to (x54t n1 n2)) (V 1)) (mnetop''' 2 (x65t n1 n2) (x76t n1 n2) (x87t n1 n2) (x98t n1 n2) (x987tft n1 n2) (x109t n1 n2) (x1087tftt n1 n2)) 
                                  (ifm (eqm (to (x54t n1 n2)) (V 2)) (mnetop''' 1 (x64tft n1 n2) (x74tftt n1 n2) (x84tf3t n1 n2) (x94tf4t n1 n2) (x94tf3tft n1 n2) (x104tf4tt n1 n2) (x104tf3tftt n1 n2)) O)).
 
 (*************************************************)                       

  
Definition q121m' n1 n2 := (ifm (eqm (to (x5tf3t n1 n2)) (V 1)) (mnetop''' 2 (x6tf4t n1 n2) (x7tf5t n1 n2) (x8tf6t n1 n2) (x9tf7t n1 n2) (x9tf6tft n1 n2)  (x10tf7tt n1 n2) (x10tf6tftt n1 n2))
                                  (ifm (eqm (to (x5tf3t n1 n2)) (V 2)) (mnetop''' 1 (x6tf3tft n1 n2) (x7tf3tftt n1 n2) (x8tf3tf3t n1 n2) (x9tf3tf4t n1 n2) (x9tf3tf3tft n1 n2) (x10tf3tf4tt n1 n2) (x10tf3tf3tftt n1 n2) )  O)).


   
  
Definition q122m' n1 n2 := (ifm (eqm (to (x5tftft n1 n2)) (V 1)) (mnetop''' 2 (x6tftf3t n1 n2) (x7tftf4t n1 n2)  (x8tftf5t n1 n2) (x9tftf6t n1 n2) (x9tftf5tft n1 n2) (x10tftf6tt n1 n2) (x10tftf5tftt n1 n2))
                                  (ifm (eqm (to (x5tftft n1 n2)) (V 2)) (mnetop''' 1 (x6tftfttft n1 n2) (x7tftfttftt n1 n2) (x8tftfttf3t n1 n2) (x9tftfttf4t n1 n2) (x9tftfttf3tft n1 n2) (x10tftfttf4tt n1 n2) ( x10tftfttf3tftt n1 n2))  O)).



  
Definition q211m' n1 n2 := (ifm (eqm (to (x5f4t n1 n2)) (V 1))   (mnetop''' 2 (x6f5t n1 n2) (x7f6t n1 n2) (x8f7t n1 n2) (x9f8t n1 n2)  (x9f7tft n1 n2) (x10f8tt n1 n2) (x10f7tftt n1 n2))
                                  (ifm (eqm (to (x5f4t n1 n2)) (V 2)) (mnetop''' 1 (x6f4tft n1 n2) (x7f4tftt n1 n2) (x8f4tf3t n1 n2) (x9f4tf4t n1 n2) (x9f4tf3tft n1 n2) (x10f4tf4tt n1 n2) (x10f4tf3tftt n1 n2)) O)).



(***************************************************)

  

Definition q221m' n1 n2:=  (ifm (eqm (to (x5ftf3t n1 n2)) (V 1)) (mnetop''' 2 (x6ftf4t n1 n2) (x7ftf5t n1 n2) (x8ftf6t n1 n2) (x9ftf7t n1 n2) (x9ftf6tft n1 n2) (x10ftf7tt n1 n2) (x10ftf6tftt n1 n2))
                                  (ifm (eqm (to (x5ftf3t n1 n2)) (V 2)) (mnetop''' 1 (x6ftf3tft n1 n2) (x7ftf3tftt n1 n2) (x8ftf3tf3t n1 n2) (x9ftf3tf4t n1 n2) (x9ftf3tf3tft n1 n2) (x10ftf3tf4tt n1 n2) ( x10ftf3tf3tftt n1 n2)) O)).


  
  
Definition q222m' n1 n2 :=  (ifm (eqm (to (x5ftftf2t n1 n2)) (V 1)) (mnetop''' 2 (x6ftftf3t n1 n2) (x7ftftf4t n1 n2) (x8ftftf5t n1 n2) (x9ftftf6t n1 n2) (x9ftftf5tft n1 n2) (x10ftftf6tt n1 n2)  (x10ftftf5tftt n1 n2))
                                  (ifm (eqm (to (x5ftftf2t n1 n2)) (V 2)) (mnetop''' 1 (x6ftftf2tft n1 n2) (x7ftftf2tftt n1 n2) (x8ftftf2tf3t n1 n2) (x9ftftf2tf4t n1 n2) (x9ftftf2tf3tft n1 n2) (x10ftftf2tf4tt n1 n2) (x10ftftf2tf3tftt n1 n2)) O)).




(*****************************************************************************************)
 
Definition q111s'' n1 n2 := (ifm  (eqm (to (x4ttt n1 n2)) (V 2))& (bacc (pk 3) (b n2 19) (r 20) (pi2 (x4ttt n1 n2))) (q111m' n1 n2)
                                     O).
 
 (*************************************************)                       

  
Definition q121s'' n1 n2 := (ifm (eqm (to (x4tftt n1 n2)) (V 2 ))& (bacc (pk 3) (b n2 11) (r 12) (pi2 (x4tftt n1 n2))) (q121m' n1 n2)
                         O).

Definition q122s'' n1 n2 := (ifm (eqm (to (x4tftft n1 n2)) (V 1 ))& (bacc (pk 3) (b n1 7) (r 8) (pi1 (x4tftft n1 n2))) (q122m' n1 n2)
                         O).
 
 
Definition q211s'' n1 n2 :=  (ifm (eqm (to (x4fttt n1 n2)) (V 1 ))& (bacc (pk 3) (b n1 23) (r 24) (pi1 (x4fttt n1 n2))) (q211m' n1 n2)
                          O).



(***************************************************)

Definition q221s'' n1 n2:=   (ifm (eqm (to (x4ftftt n1 n2)) (V 2 ))& (bacc (pk 3) (b n2 9) (r 10) (pi2 (x4ftftt n1 n2))) (q221m' n1 n2)
                           O).
Definition q222s'' n1 n2 :=  (ifm (eqm (to (x4ftftft n1 n2)) (V 1 ))& (bacc (pk 3) (b n1 13) (r 14) (pi1 (x4ftftft n1 n2))) (q222m' n1 n2) O).


 
(*****************************************)
  
Definition q11_m' n1 n2 :=  (ifm  (eqm (to (x3tt n1 )) (V 2)) (q111s'' n1 n2)
                                      O).
 
Definition q12_m' n1 n2 := (ifm (eqm (to (x3tft n1 n2)) (V 1))& (bacc (pk 3) (b n1 7) (r 8) (pi2 (x3tft n1 n2))) (q121s'' n1 n2)
                                    (ifm (eqm (to (x3tft n1 n2)) (V 2))& (bacc (pk 3) (b n2 11) (r 12) (pi2 (x3tft n1 n2))) (q122s'' n1 n2)
                                                 O)).
 

Definition q21_m' n1 n2 := (ifm  (eqm (to (x3ftt n2)) (V 1))  (q211s'' n1 n2)
                                   O).

Definition q22_m' n1 n2  := (ifm (eqm (to (x3ftft n1 n2)) (V 1))& (bacc (pk 3) (b n1 13) (r 14) (pi1 (x3ftft n1 n2))) (q221s'' n1 n2)
                                    (ifm (eqm (to (x3ftft n1 n2)) (V 2))& (bacc (pk 3) (b n2 9) (r 10) (pi2 (x3ftft n1 n2))) (q222s'' n1 n2)
                                                   O)).
 
(********************************************************************************************)

Definition q1_m' n1 n2 := (ifm (eqm (to (x2t n1 )) (V 1))& (bacc (pk 3) (b n1 7) (r 8) (pi1 (x2t n1 )))  (q11_m' n1 n2)
			           (ifm (eqm (to (x2t n1 )) (V 2))  (q12_m' n1 n2)
                                                  O)).
 
Definition q2_m' n1 n2 :=  (ifm (eqm (to (x2ft n2)) (V 2))& (bacc (pk 3) (b n2 9) (r 10) (pi2 (x2ft n2)))  (q21_m' n1 n2)
			           (ifm (eqm (to (x2ft n2)) (V 1))  (q22_m' n1 n2)
                                                   O)).
 


Definition t9 n1 n2 :=  (ifm (eqm (to x1) (V 1)) (q1_m' n1 n2)
		    	           (ifm (eqm (to x1) (V 2))  (q2_m' n1 n2)
                                                   O )).

Definition phi10 n1 n2 := (phi9 n1 n2) ++ [msg (t9 n1 n2)] .











