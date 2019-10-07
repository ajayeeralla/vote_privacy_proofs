Load "foo_axioms".
  
    
(** * FOO Voting Prtocol *)
(** ** Phase-I *)
(** 
- V -> A : (V, sign(blind(commit(v, r), r'), sk(V)))

- A-> V :  sign(blind(commit(v, r), r'), sk(A)) *)

 
(** - We assume that Administrator and collector are dishonest
    - Hence, random numbers used to generate keys (pair) of them included in attacker's knowledge *)

(** * ProtocolPhase-I: There are two voters [V1] and [V2], and their corresponding votes [va] and [vb] respectively. *)
 
(** * Frame [phi0]: initial knowledge *)
(** 1-Voter1, 2-Voter2, 3-Administrator, 4-Collector, 5-Mixnet 
[(pk 0)] represents a public key used in commitment shceme. *) 
 
  
Definition vt (n:nat) := (v (N n)).
Definition phi0:= [msg (pk 1); msg (pk 2);  msg (pk 3); msg (N 4); msg (pk 5); msg (N 6)].

(** * Frame [phi11] *)

(** commitments *) 
 
Definition b (n' n'':nat) := (commit (v (N n')) (r n'')).
Definition e (t:message) (n':nat) := (blind t (pk 3) (r n')).


(** Converting [mylist] to [list message] *)
 

Definition mphi0 := (conv_mylist_listm phi0).

(** attacker's computation *)

Definition x1 := (f mphi0).  
 
   
Definition q0 n1 n2 :=  (ifm (eqm (to x1) (V 1)) ((pk 1), ((e (b n1 7) 8) , (sign (sk 1) (ONE, (e (b n1 7) 8)))))
		    	            (ifm  (eqm (to x1) (V 2))  ((pk 2), ( (e (b n2 9) 10),  (sign (sk 2) (ONE, (e (b n2 9) 10)))))
                                                    O)).
                                                                     

(** attacker's knowledge *)

Definition phi1 n1 n2 := phi0 ++ [msg (q0 n1 n2)].

(** * Frame [phi2] *)
Fixpoint traces {n} (l:mylist n) : list (list oursum):= cons (ifmT l) (cons (ifmE l) nil).


Eval compute in ifmT (phi1 0 1).
Eval compute in (ifmT (conv_listos_mylist (ifmE (phi1 0 1)))).
Eval compute in (ifmE (conv_listos_mylist (ifmE (phi1 0 1)))).
Definition phi1t n1 := phi0 ++ [msg ((pk 1), ((e (b n1 7) 8) , (sign (sk 1) (ONE, (e (b n1 7) 8)))))]. 
Definition x2t n1 := (f (conv_mylist_listm (phi1t n1))). 
 
Definition phi1ft  n2 := phi0 ++ [msg  ((pk 2), ( (e (b n2 9) 10),  (sign (sk 2) (ONE, (e (b n2 9) 10)))))].

Definition x2ft n2 := (f (conv_mylist_listm (phi1ft n2))).

(**************************************************************************)
Definition mphi1 n1 n2 := (conv_mylist_listm (phi1 n1 n2)).
Definition x2 n1 n2 := (f (mphi1 n1 n2)).  


Definition q1 n1 n2 := (ifm (eqm (to (x2t n1)) (V 1))& (bacc (pk 3) (b n1 7) (r 8) (pi1 (x2t n1)))  ok 
			            (ifm (eqm (to (x2t n1)) (V 2))  ((pk 2), ( (e (b n2 11) 12),  (sign (sk 2) (ONE, (e (b n2 11) 12)))))
                                                  O)). 
 
Definition q2 n1 n2 :=  (ifm (eqm (to (x2ft n2)) (V 2))& (bacc (pk 3) (b n2 9) (r 10) (pi2 (x2ft n2)))  ok  
			           (ifm (eqm (to (x2ft n2)) (V 1))  ((pk 1), ( (e (b n1 13) 14),  (sign (sk 1) (ONE, (e (b n1 13) 14)))))
                                                   O)).
 
Definition t1 n1 n2 :=  (ifm (eqm (to x1) (V 1)) (q1 n1 n2)
		    	     (ifm (eqm (to x1) (V 2))  (q2 n1 n2) O)).

Definition phi2 n1 n2 := (phi1 n1 n2) ++ [msg (t1 n1 n2)].


 (** * Frame [phi3] *)
   (** T *)
   
Definition phi2tt n1 := (phi1t n1) ++ [msg ok]. 
Definition x3tt n1 := (f (conv_mylist_listm (phi2tt n1))). 

Definition phi2tft n1 n2 := (phi1t n1) ++ [msg ((pk 2), ( (e (b n2 11) 12),  (sign (sk 2) (ONE, (e (b n2 11) 12)))))].                                       
Definition x3tft n1 n2 := (f (conv_mylist_listm (phi2tft n1 n2))).

(** FT *)

Definition phi2ftt n2 := (phi1ft n2) ++ [msg ok].  
Definition x3ftt n2 := (f (conv_mylist_listm (phi2ftt n2))). 
 
Definition phi2ftft n1 n2  := (phi1ft n2) ++ [msg  (pk 1, (e (b n1 13) 14, sign (sk 1) (ONE, (e (b n1 13) 14))))].
Definition x3ftft n1 n2 := (f (conv_mylist_listm (phi2ftft n1 n2))). 

Eval compute in x3ftft  0 1.
Eval compute in x3ftft 1 0.

(****************************************************************)
Definition mphi2 n1 n2:= (conv_mylist_listm (phi2 n1 n2)).
Definition x3 n1 n2 := (f (mphi2 n1 n2)). 

Definition q11 n1 n2 :=  (ifm  (eqm (to (x3tt n1 )) (V 2))  ((pk 2), ( (e (b n2 19) 20),  (sign (sk 2) (ONE, (e (b n2 19) 20))))) O).
                                     
 
Definition q12 n1 n2 := (ifm (eqm (to (x3tft n1 n2)) (V 1))& (bacc (pk 3) (b n1 7) (r 8) (pi1 (x3tft n1 n2))) ok
                                    (ifm (eqm (to (x3tft n1 n2)) (V 2))& (bacc (pk 3) (b n2 11) (r 12) (pi2 (x3tft n1 n2))) ok
                                                  O)).
 

Definition q21 n1 n2 := (ifm  (eqm (to (x3ftt n2)) (V 1))  ((pk 1), ( (e (b n1 23) 24),  (sign (sk 1) (ONE, (e (b n1 23) 24)))))
                                    O).

Definition q22 n1 n2 := (ifm (eqm (to (x3ftft n1 n2 )) (V 1))& (bacc (pk 3) (b n1 13) (r 14) (pi1 (x3ftft n1 n2 ))) ok
                                    (ifm (eqm (to (x3ftft n1 n2 )) (V 2))& (bacc (pk 3) (b n2 9) (r 10) (pi2 (x3ftft n1 n2 ))) ok
                                                    O)).
 

 
(********************************************************************************************)

Definition q1_s n1 n2 := (ifm (eqm (to (x2t n1)) (V 1))& (bacc (pk 3) (b n1 7) (r 8) (pi1 (x2t n1 )))  (q11 n1 n2)
			           (ifm (eqm (to (x2t n1 )) (V 2))  (q12 n1 n2)
                                                   O)).
 
Definition q2_s n1 n2 :=  (ifm (eqm (to (x2ft  n2)) (V 2))& (bacc (pk 3) (b n2 9) (r 10) (pi2 (x2ft  n2)))  (q21 n1 n2 )
			           (ifm (eqm (to (x2ft  n2)) (V 1))  (q22 n1 n2)
                                                   O)).
 
Definition t2 n1 n2 :=  (ifm (eqm (to x1) (V 1)) (q1_s n1 n2)
		    	           (ifm (eqm (to x1) (V 2))  (q2_s n1 n2)
                                                   O)).

Definition phi3  n1 n2 := (phi2 n1 n2) ++ [msg (t2 n1 n2)].
(** * Frame [phi4] *)
Definition mphi3ttt n1 n2 := (phi2tt n1) ++ [msg ((pk 2), ( (e (b n2 19) 20),  (sign (sk 2) (ONE, (e (b n2 19) 20)))))].
Definition x4ttt n1 n2 := (f (conv_mylist_listm (mphi3ttt n1 n2))). 

Definition phi3tftt n1 n2 := (phi2tft n1 n2) ++ [msg ok].
Definition x4tftt n1 n2 := (f (conv_mylist_listm (phi3tftt n1 n2))).

Definition phi3tftft n1 n2 := (phi2tft n1 n2) ++ [msg ok].
Definition x4tftft n1 n2 := (f (conv_mylist_listm (phi3tftft n1 n2))).

Definition phi3fttt n1 n2 := (phi2ftt n2) ++ [msg  ((pk 1), ( (e (b n1 23) 24),  (sign (sk 1) (ONE, (e (b n1 23) 24)))))].

Definition x4fttt n1 n2 := (f (conv_mylist_listm (phi3fttt n1 n2))).

Definition phi3ftftt n1 n2:= (phi2ftft n1 n2) ++ [msg ok].
Definition x4ftftt n1 n2 := (f (conv_mylist_listm (phi3ftftt n1 n2))).
Definition phi3ftftft n1 n2:= (phi2ftft n1 n2) ++ [msg ok].
Definition x4ftftft n1 n2 := (f (conv_mylist_listm (phi3ftftft n1 n2))).

(**********************************)
Definition q111 n1 n2 := (ifm  (eqm (to (x4ttt n1 n2)) (V 2))& (bacc (pk 3) (b n2 19) (r 20) (pi2 (x4ttt n1 n2))) ok
                                     O).
 
 
 (*************************************************)                       

  
Definition q121 n1 n2 := (ifm (eqm (to (x4tftt n1 n2)) (V 2 ))& (bacc (pk 3) (b n2 11) (r 12) (pi2 (x4tftt n1 n2))) ok
                         O).

Definition q122 n1 n2 := (ifm (eqm (to (x4tftft n1 n2)) (V 1 ))& (bacc (pk 3) (b n1 7) (r 8) (pi1 (x4tftft n1 n2))) ok
                         O).
 
 
Definition q211 n1 n2 :=  (ifm (eqm (to (x4fttt n1 n2)) (V 1 ))& (bacc (pk 3) (b n1 23) (r 24) (pi1 (x4fttt n1 n2))) ok
                          O).



(***************************************************)

Definition q221 n1 n2:=   (ifm (eqm (to (x4ftftt n1 n2)) (V 2 ))& (bacc (pk 3) (b n2 9) (r 10) (pi2 (x4ftftt n1 n2))) ok
                           O).
Definition q222 n1 n2 :=  (ifm (eqm (to (x4ftftft n1 n2)) (V 1 ))& (bacc (pk 3) (b n1 13) (r 14) (pi1 (x4ftftft n1 n2))) ok O).


 
(*****************************************)
  
Definition q11_s n1 n2 :=  (ifm  (eqm (to (x3tt n1 )) (V 2)) (q111 n1 n2)
                                      O).
 
Definition q12_s n1 n2 := (ifm (eqm (to (x3tft n1 n2)) (V 1))& (bacc (pk 3) (b n1 7) (r 8) (pi1 (x3tft n1 n2))) (q121 n1 n2)
                                    (ifm (eqm (to (x3tft n1 n2)) (V 2))& (bacc (pk 3) (b n2 11) (r 12) (pi2 (x3tft n1 n2))) (q122 n1 n2)
                                                 O)).
 

Definition q21_s n1 n2 := (ifm  (eqm (to (x3ftt n2)) (V 1))  (q211 n1 n2)
                                   O).

Definition q22_s n1 n2  := (ifm (eqm (to (x3ftft n1 n2)) (V 1))& (bacc (pk 3) (b n1 13) (r 14) (pi1 (x3ftft n1 n2))) (q221 n1 n2)
                                    (ifm (eqm (to (x3ftft n1 n2)) (V 2))& (bacc (pk 3) (b n2 9) (r 10) (pi2 (x3ftft n1 n2))) (q222 n1 n2)
                                                   O)).
 
(********************************************************************************************)

Definition q1_ss n1 n2 := (ifm (eqm (to (x2t n1 )) (V 1))& (bacc (pk 3) (b n1 7) (r 8) (pi1 (x2t n1 )))  (q11_s n1 n2)
			           (ifm (eqm (to (x2t n1 )) (V 2))  (q12_s n1 n2)
                                                  O)).
 
Definition q2_ss n1 n2 :=  (ifm (eqm (to (x2ft n2)) (V 2))& (bacc (pk 3) (b n2 9) (r 10) (pi2 (x2ft n2)))  (q21_s n1 n2)
			           (ifm (eqm (to (x2ft n2)) (V 1))  (q22_s n1 n2)
                                                   O)).
 


Definition t3 n1 n2 :=  (ifm (eqm (to x1) (V 1)) (q1_ss n1 n2)
		    	           (ifm (eqm (to x1) (V 2))  (q2_ss n1 n2)
                                                   O )).

Definition phi4 n1 n2 := (phi3 n1 n2) ++ [msg (t3 n1 n2)].



 

 (** Tactics *)


 
Ltac unf_phi := try unfold phi0, phi1, phi2. (* phi3 phi4,  phi5.*)
 
Ltac unf_q :=  try unfold q0, q1, q2. 
Ltac unf_trm:=  try unfold t1. (*t2, t3, t4.*)

Ltac unf := try unf_phi; try unf_trm; try unf_q.


 (** blindness *) 
Ltac aply_blindness n n1 n2 n3 n4 m0 m1 t1 t2 l  := pose proof( blindness n n1 n2 n3 n4 m0 m1 t1 t2 l ) as H.

(** Using [funapptrmhyp] *)
Ltac appconst H:=
  funappmconst ok H; funappmconst (V 1) H; funappmconst (V 2) H; funappmconst O H; funappmconst ONE H; funappmconst TWO H; funappmconst THREE H;  funappbconst FAlse H; try reflexivity.
 Ltac x1checks x1 x2 H := funapptrmhyp (msg x1) (msg x2) H ;
                   funapptrmhyp (msg (to x1)) (msg (to x2)) H; 
                    funapptrmhyp (bol (eqm (to x1) (V 1))) (bol (eqm (to x2) (V 1))) H;
                   funapptrmhyp (bol (eqm (to x1) (V 2))) (bol (eqm (to x2) (V 2))) H; 
                   funapptrmhyp (bol (eqm (to x1) (pk 3))) (bol (eqm (to x2) (pk 3))) H; try reflexivity.
  
Axiom fresh_blind : forall (n1 n2 n3 n4 n5 n6 n7 : nat) {n} (l1 l2 :mylist n),
                      (l1 ++ [msg (e (b n1 n2) n3)]) ~ (l2 ++ [msg (e (b n4 n5) n6)]) ->  Fresh [n7] (l1 ++ [msg (e (b n1 n2) n3)] ++  l2 ++ [msg (e (b n4 n5) n6)]) = true  -> (l1 ++ [msg (e (b n1 n2) n7)])  ~ (l2 ++ [msg (e (b n4 n5) n7)]).
Axiom fresh_commit : forall (n1 n2 n3 n4 n5 n6 n7 : nat) {n} (l1 l2 :mylist n), Fresh [n7] (l1++ [msg (e (b n1 n2) n3)] ++  l2 ++ [msg (e (b n4 n5) n6)]) = true ->
                      (l1 ++ [msg (e (b n1 n2) n3)]) ~ (l2 ++ [msg (e (b n4 n5) n6)]) -> (l1 ++ [msg (e (b n1 n7) n3)]) ~ (l2 ++ [msg (e (b n4 n7) n6)]). 
  
 Ltac adminchecks t1 t2 H:=
  funapptrmhyp (msg (pi1 t1)) (msg (pi1 t2)) H;
  funapptrmhyp (msg (pi1 (pi1 t1))) (msg (pi1 (pi1 t2))) H;
  funapptrmhyp (msg (pi2 (pi1 t1))) (msg (pi2 (pi1 t2))) H;
  funapptrmhyp (msg (pi1 (pi2 (pi1 t1)))) (msg (pi1 (pi2 (pi1 t2)))) H;
  funapptrmhyp (msg (pi2 (pi2 (pi1 t1)))) (msg (pi2 (pi2 (pi1 t2)))) H;
  funapptrmhyp (msg (pi2 t1)) (msg (pi2 t2)) H;
  funapptrmhyp (msg (pi1 (pi2 t1))) (msg (pi1 (pi2 t2))) H;
  funapptrmhyp (msg (pi2 (pi2 t1))) (msg (pi2 (pi2 t2))) H;
  funapptrmhyp (msg (pi1 (pi2 (pi2 t1)))) (msg (pi1 (pi2 (pi2 t2)))) H;
  funapptrmhyp (msg (pi2 (pi2 (pi2 t1)))) (msg (pi2 (pi2 (pi2 t2)))) H;
   funapptrmhyp (msg (bsign (sk 3) (pi1 (pi2 (pi1 t1))) )) (msg (bsign (sk 3) (pi1 (pi2 (pi1 t2))) )) H;
  funapptrmhyp (msg (bsign (sk 3) (pi1 (pi2 (pi2 t1))) )) (msg (bsign (sk 3) (pi1 (pi2 (pi2 t2))) )) H;
  funapptrmhyp (msg ((bsign (sk 3) (pi1 (pi2 (pi1 t1))) ) , (bsign (sk 3) (pi1 (pi2 (pi2 t1))) ))) (msg ((bsign (sk 3) (pi1 (pi2 (pi1 t2))) ), (bsign (sk 3) (pi1 (pi2 (pi2 t2))) ))) H; 
 funapptrmhyp (bol (ver (pk 1)  (pi1 (pi2 (pi1 t1))) (pi2 (pi2 (pi1 t1))))) (bol (ver (pk 1)  (pi1 (pi2 (pi1 t2))) (pi2 (pi2 (pi1 t2))))) H;
 funapptrmhyp (bol (ver (pk 2)  (pi1 (pi2 (pi2 t1))) (pi2 (pi2 (pi2 t1)))))  (bol (ver (pk 2)  (pi1 (pi2 (pi2 t2))) (pi2 (pi2 (pi2 t2))))) H.

 
   Ltac funapp_vtrm a v1 v2 ck bk m H  := 
funapptrmhyp (msg (m, (e (b v1 ck) bk))) (msg (m, (e (b v2 ck) bk))) H;
     funapptrmhyp (msg (sign (sk a) (m, (e (b v1 ck) bk))))  (msg (sign (sk a) (m, (e (b v2 ck) bk)))) H; 
 funapptrmhyp  (msg ((e (b v1 ck) bk), (sign (sk a) (m, (e (b v1 ck) bk)))))  (msg ((e (b v2 ck) bk), (sign (sk a) (m, (e (b v2 ck) bk))))) H;
 funapptrmhyp  (msg (pk a, ((e (b v1 ck) bk), (sign (sk a) (m, (e (b v1 ck) bk))))))  (msg (pk a, ((e (b v2 ck) bk), (sign (sk a) (m, (e (b v2 ck) bk)))))) H; try reflexivity.
   Ltac bacctac v1 v2 ck bk t1 t2 H:=
      funapptrmhyp (msg (pi1 t1)) (msg (pi1 t2)) H; 
     funapptrmhyp (bol (bacc (pk 3) (b v1 ck) (r bk) (pi1 t1))) (bol (bacc (pk 3) (b v2 ck) (r bk) (pi1 t2))) H;
    funapptrmhyp (msg (pi2 t1)) (msg (pi2 t2)) H; 
    funapptrmhyp (bol (bacc (pk 3) (b v1 ck) (r bk) (pi2 t1))) (bol (bacc (pk 3) (b v2 ck) (r bk) (pi2 t2))) H; try reflexivity.
(** tactics related to application of unforgeability *)
   (*
    Ltac rew_hyps  :=       
       match goal with
         | [H:_ |- _ ] => simpl in H; repeat rewrite H; unfold andB; repeat redg; clear H
       end. *)
       Ltac ufcma_pi1  x :=
          match goal with
            |[|- context[(ver (pk ?n) (pi1 (pi2 (pi1 x))) ?Y)] ] => pose proof( UFCMA n (pi1 (pi2 (pi1 x))) Y); rew_hyps; try split; try reflexivity
          end. 
             Ltac ufcma_pi2 x:=  
               match goal with
                 |[|- context[(ver (pk ?n1) (pi1 (pi2 (pi2 x))) ?Y)] ] => pose proof( UFCMA n1 (pi1 (pi2 (pi2 x))) Y); rew_hyps; try split; try reflexivity 
               end.
(** andB elimination *)
             
Axiom andB_elm': forall (b1 b2: Bool) (x y : message), (ifm b1& b2 x y) #  (ifm b1 (ifm b2 x y ) y).

Ltac aply_andB_elm := 
match goal with 
|[|- context[ifm (ifb ?B1 ?B2 FAlse) ?T1 ?T2 ] ] => rewrite andB_elm' with (b1:= B1) (b2:= B2) (x:= T1) (y:= T2)
end. 
Ltac ufcma_pi1'  x :=
          repeat match goal with
            |[|- context[(ver (pk ?n') (pi1 (pi2 (pi1 x))) ?Y)] ] => rewrite UFCMA with (n:= n') (t:= (pi1 (pi2 (pi1 x)))) (u:= Y)   ;  simpl ; repeat (try rewrite IFSAME_B; try rewrite IFFALSE_B; try rewrite IFFALSE_M); try split; try reflexivity
          end. 
  
      Ltac ufcma_pi2' x:=  
              repeat match goal with
                       |[|- context[(ver (pk ?n1) (pi1 (pi2 (pi2 x))) ?Y)] ] => rewrite UFCMA with (n:=n1) (t:= (pi1 (pi2 (pi2 x)))) (u:= Y)  ; simpl ; repeat (try rewrite IFSAME_B; try rewrite IFFALSE_B; try rewrite IFFALSE_M); try split; try reflexivity
                     end.                                                                                                                                                              Ltac unforge' x1 n1 n2:= 
                         ufcma_pi1' (x1 n1 n2); ufcma_pi2' (x1 n1 n2);   ufcma_pi1' (x1 n2 n1);   ufcma_pi2' (x1 n2 n1).
                       
Ltac aply_andB_elm' B2 := 
match goal with 
|[|- context[ifm (ifb ?B1 B2 FAlse) ?T1 ?T2 ] ] => rewrite andB_elm' with (b1:= B1) (b2:= B2) (x:= T1) (y:= T2)
end. 
 Ltac aply_bver' := 
  match goal with
    |[|- context[bver (pk ?N) ?T  (unblind ?T (pk ?N) ?T' ?U) ] ] => rewrite SHU_UFCMA with (n:= N) (t:=T) (t':= T') (u:= U) 
  end.
 Ltac btrm n x1 b1 x2 b2  H :=  
  funapptrmhyp (bol (ifb (eqm (pi1 (pi2 x1)) b1)
            (ver (pk n) b1 (pi2 (pi2 x1))) FAlse)) (bol (ifb (eqm (pi1 (pi2 x2)) b2) (ver (pk n) b2 (pi2 (pi2 x2))) FAlse)) H.
(** replace bacc with bver *)

Ltac rew_mupbver  :=
  match goal with
    | [|- context[ (ifm (bacc (pk 3) ?M _ ?T) ?T1 ?T2) ] ] => rewrite mupbver with (n := 3) (m:= M)  (t1:= T1) (t2:= T2)
  end. 
 Ltac aply_bver := 
  match goal with
    |[|- context[bver (pk ?N) ?T  (unblind ?T (pk ?N) ?T' ?U) ] ] => pose proof (SHU_UFCMA N T T' U) 
  end.
             
(** replacing the random commit keys with fresh values *)
 
Definition droplast {n} (l: mylist n): mylist (pred n) :=  (reverse (dropone (reverse l))).
Axiom restr_droplast : forall {n} (l1 l2:mylist n), (l1 ~ l2) -> (droplast l1) ~ (droplast l2). 
Ltac droplast_in H:= apply restr_droplast in H; unfold droplast in H; simpl in H.
Ltac fresh_n n3 n4 H := apply FRESHIND_rs with (n1:= n3) (n2:= n4) in H; try split; try reflexivity.
Ltac app_rn n3 n4 H := 
funapptrmhyp (msg (r n3)) (msg (r n4)) H;  try reflexivity. 
Ltac fresh_rn n1 n2 H := fresh_n n1 n2 H; try split; try reflexivity; app_rn n1 n2 H; try split; try reflexivity.

      (*                  funapptrmhyp (msg (r n3)) (msg (r n4)) H;  repeat try split;    try reflexivity. 
*)

                       
  Ltac fresh_assert name  :=
  match goal with
    | [H: (?X ~ ?Y) |- _ ] =>  assert(([msg (vt 0); msg (vt 1)] ++ Y) ~ ([msg (vt 0); msg (vt 1)] ++ Y)) as name ;try reflexivity; do 4 (droplast_in name)
  end.
  
 

  Ltac appcommit v  n1 n2  H:=
    funapptrmhyp (msg (b v n1)) (msg (b v n2)) H; try reflexivity.
  
  Ltac appblind v  n1 n2  r  H:=
    funapptrmhyp (msg (e (b v n1) r)) (msg (e (b v n2) r )) H; try reflexivity.
  
   Ltac freshind n1 n2 H:= fresh_rn n1 n2 H; fresh_rn (S n1) (S n1) H; try split; try reflexivity.
  

 
 
  Ltac assertg fr1 fr2 t :=
    match goal with
      | [H : (?X1 ~ ?X2) |- _ ] => match H with
                                     |fr1 =>  match goal with
                                                | [H1: (?X3 ~ ?X4) |- _ ] => match H1 with
                                                                               | fr2 => assert( X1 ~ X3) as t ;simpl
                                                                             end
                                              end
                                   end
                                     
                                    
    end.
  Ltac aplytrans H1 :=
    match goal with
      | [H: (?X1~ ?X2) |- _ ] => match H with
                              | H1 => apply EQI_trans with (ml2:= X2); try assumption; symmetry; assumption
                            end
    end.


  Ltac freshns1 v1 v2  n1 n2 n3 n4 H :=
    fresh_assert H; freshind n1 n2 H; freshind n3 n4 H; appcommit v1 n3 n4 H; appcommit v2 n1 n2 H; appblind v2 n1 n2 (S n3) H; appblind v1 n3 n4 (S n1) H;  do 6 (dropone_in H); do 5  (restrproj_in 11 H).
    
  Ltac freshns2 v1 v2 n1 n2 n3 n4 H :=
    fresh_assert H; freshind n1 n2 H; freshind n3 n4 H; appcommit v1 n1 n2 H; appcommit v2 n3 n4 H; appblind v2 n3 n4 (S n3) H; appblind v1 n1 n2 (S n1) H;  do 6 (dropone_in H); do 4  (restrproj_in 11 H).
   Ltac freshns v1 v2 n1 n2 n3 n4 H1 H2 :=  freshns1 v1 v2 n1 n2 n3 n4 H1; freshns2 v1 v2 n1 n4 n3 n2 H2 .
   

   Ltac asert_aplytrans H1 H2 t := assertg  H1 H2 t ; try aplytrans H1; try assumption; symmetry in t. 
    (** tactics to replace fresh names in commitments *)
     
   (** (b v2 n1) -> (b v2 n3),  (b v1 n3) -> (b v1 n1) *)
Ltac rep_commits  v1 v2 n1 n2 n3 n4 H1 H2 H3 H H0 :=  freshns v1 v2 n1 n2 n3 n4 H1 H2; (restrproj_in 11 H) ;
   asert_aplytrans H1 H2 H3 ;
   asert_aplytrans H H3 H0; symmetry in H0;
   clear -H0.
(** building the term when verification successful *)

 Ltac ver_suc n x1 e1 x2 e2 H:=
  funapptrmhyp (bol (eqm (pi1 (pi2 x1)) e1)) (bol (eqm (pi1 (pi2 x2)) e2)) H;
  funapptrmhyp (bol  (ver (pk n) e1 (pi2 (pi2 x1))))  (bol (ver (pk n) e2 (pi2 (pi2 x2)))) H;
  funapptrmhyp (bol (eqm (pi1 (pi2 x1)) e1) & (ver (pk n) e1 (pi2 (pi2 x1))))  (bol (eqm (pi1 (pi2 x2)) e2) & (ver (pk n) e2 (pi2 (pi2 x2)))) H.
Ltac ver_suc1 n x1 e1 x2 e2 H:=
  funapptrmhyp (bol (eqm (pi1 (pi2 x1)) e1)) (bol (eqm (pi1 (pi2 x2)) e2)) H;
  funapptrmhyp (bol  (ver (pk n) e1 (pi2 (pi2 x1))))  (bol (ver (pk n) e2 (pi2 (pi2 x2)))) H.
 (** apply unforgeability *)

Ltac unforge x1 n1 n2:=
  ufcma_pi1 (x1 n1 n2); ufcma_pi2 (x1 n1 n2);   ufcma_pi1 (x1 n2 n1);   ufcma_pi2 (x1 n2 n1).

Axiom EQL_eqm : forall u u', (EQL u u') ##  (eqm (L u) (L u')).
Check L. 
 (** lengths of the encryptions are equal *)
Axiom len_nonce: forall n n', (L n) # (L n').

Axiom len_f1 : forall t t' f, (L t) # (L t') -> (L (f t)) # (L (f t')).
Axiom len_f2 : forall t1 t2 t1' t2' f, (L t1) # (L t1') -> (L t2) # (L t2')  -> (L (f t1 t2)) # (L (f t1' t2')).
Axiom len_f3 : forall t1 t2 t3  t1' t2' t3' f, (L t1) # (L t1') -> (L t2) # (L t2') -> (L t3) # (L t3') -> (L (f t1 t2 t3)) # (L (f t1' t2' t3')).
Axiom len_f4 : forall t1 t2 t3 t4 t1' t2' t3' t4' f, (L t1) # (L t1') -> (L t2) # (L t2') -> (L t3) # (L t3') -> (L t4) # (L t4') -> (L (f t1 t2 t3 t4)) # (L (f t1' t2' t3' t4')).


Axiom ENCCPA': forall (u u' u'': message) (n n1 n2 n3 :nat) {m} (l:mylist m),  (eqm (L u) (L u')) ## TRue ->   (leb (length (distmvars l)) 1) = true -> (clos_listm [u; u'; u''] = true) -> ((Fresh [n2] l) = true) -> ((Fresh [n3] l) = true) -> ((checkmtmylis (sk n1) l) = false)  -> (l++ [msg (enc u (pk n1) (rr (N n2)))]) ~ (l++ [msg (enc u' (pk n1) (rr (N n3)))]).
(** include cor_ex7_2.v *) 
Axiom EQmsg': forall(x y: message),   x # y <->   (eqm x y) ## (TRue) .
  Ltac bterm v1 v2 ck H :=
  funapptrmhyp (msg (e (b v1 ck) (S ck))) (msg (e (b v2 ck) (S ck))) H.
