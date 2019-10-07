(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                     Rohit Chadha <chadhar@missouri.edu>              *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)
Load "ex7_12".
(** This library defines auxiliary theorems which will be used in the proofs of real-or-random secrecy of Diffie-Hellman (DH) protocol and authentication of (STS) protocol . *)

Theorem mor_eval_andB : forall (n1 : nat) (t1 t2:message), (if_then_else_M (Bvar n1)& (Bvar (n1+1)) t1 t2) #
(if_then_else_M (Bvar n1) (if_then_else_M (Bvar (n1+1)) ((n1+1):=TRue)((n1:=TRue)t1) ((n1+1):=FAlse)((n1:=TRue)t2)) (((n1:=FAlse)t2))).

Proof. intros.
unfold andB.
rewrite <- IFSAME_M with (b:= (Bvar n1)) (x:=  (if_then_else_M (if_then_else_B (Bvar n1) (Bvar (n1+1)) FAlse) t1 t2)) .
rewrite IFEVAL_M .
simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_B.
rewrite IFFALSE_B.
rewrite IFFALSE_M.
assert(H: (beq_nat (n1+1) n1 = false)).
rewrite Nat.eqb_sym.
induction n1.
reflexivity.
simpl. auto.
rewrite H.
rewrite IFEVAL_M with (n:= (n1+1)).
reflexivity.
Qed.

(*corollary**)
Axiom mor_eval_andB' : forall (b1 b2 : Bool) (t1 t2 : message) , (if_then_else_M b1 & b2 t1 t2 ) # (if_then_else_M b1 (if_then_else_M b2 (subbol_msg' b2 TRue (subbol_msg' b1 TRue t1))  (subbol_msg' b2 FAlse (subbol_msg' b1 TRue t2))) (subbol_msg' b1 FAlse t2)).

Theorem breq_msgeq: forall (n:nat) (m1 m2 m3 m4 :message) , ((n:= TRue)m1)# ((n:= TRue)m3) -> ((n:= FAlse)m2)# ((n:= FAlse)m4) -> (if_then_else_M (Bvar n) m1 m2) # (if_then_else_M (Bvar n) m3 m4).
Proof. intros.
rewrite IFEVAL_M. rewrite H. rewrite H0. rewrite IFEVAL_M with (t1:= m3) (t2:= m4).
reflexivity. Qed.

(*Corollary*)
Theorem breq_msgeq': forall (  b :Bool) (m1  m2 m3 m4 :message) ,  (subbol_msg' b TRue m1) # (subbol_msg' b TRue m2) -> (subbol_msg' b FAlse m3) # (subbol_msg' b FAlse m4) -> (if_then_else_M b m1 m3) # (if_then_else_M b m2 m4).

Proof. intros.
rewrite IFEVAL_M'.
rewrite IFEVAL_M' with (t1:= m2).
rewrite H, H0.
reflexivity.
Qed.
(*using (Bvar n)*)
Theorem breq_msgeq'': forall (n:nat) (m1  m2 m3 m4 :message) ,  (subbol_msg n TRue m1) # (subbol_msg n TRue m2) -> (subbol_msg n FAlse m3) # (subbol_msg n FAlse m4) -> (if_then_else_M (Bvar n) m1 m3) # (if_then_else_M (Bvar n) m2 m4).

Proof. intros.
rewrite IFEVAL_M.
rewrite IFEVAL_M with (t1:= m2).
rewrite H, H0.
reflexivity.
Qed.

Axiom breq_msgeq''': forall (n:nat) (b:Bool) (m1  m2 m3 m4 :message) ,  (if_then_else_M (Bvar n) m1 m3) # (if_then_else_M (Bvar n) m2 m4) ->   (if_then_else_M b m1 m3) # (if_then_else_M b m2 m4).

(* then branches are equal*)
Axiom breq_msgeq1: forall (n:nat) ( m2 m3 m4 :message) ,  ((n:= FAlse)m2)# ((n:= FAlse)m4) -> (if_then_else_M (Bvar 1) m3 m2) # (if_then_else_M (Bvar n) m3 m4).

 Theorem breq_msgeq1': forall (  b :Bool) ( m2 m3 m4 :message) ,  (subbol_msg' b FAlse m2) # (subbol_msg' b FAlse m4) -> (if_then_else_M b m3 m2) # (if_then_else_M b m3 m4).

Proof. intros . rewrite IFEVAL_M'.
rewrite IFEVAL_M' with (t2:= m4).
rewrite H.
reflexivity.
Qed.

Theorem  andB_elm : forall (n1 n2 : nat) (x y: message), (if_then_else_M (Bvar n1) &  (Bvar n2) x y) # (if_then_else_M (Bvar n1) (if_then_else_M (Bvar n2) x y) y).
Proof. intros.
rewrite <- IFSAME_M with (b:= (Bvar n1)) (x:= (if_then_else_M (Bvar n1) & (Bvar n2) x y)) at 1. 
rewrite IFEVAL_M with (n:= n1). simpl. 
rewrite <- beq_nat_refl.
Eval compute in subbol_msg' (Bvar n1) TRue x.

rewrite IFEVAL_M with (n:= n1) (t2:= y).
simpl.
 rewrite IFTRUE_B, IFFALSE_B, IFFALSE_M.
reflexivity .
Qed.

(** Eliminating [andB] in a term *)
Axiom andB_elm': forall (b1 b2: Bool) (x y : message), (if_then_else_M b1& b2 x y) #  (if_then_else_M b1 (if_then_else_M b2 x y ) y).

Theorem  breq_msgeq_andB : forall (n1 n2:nat) (m1 m2 m1' m2' :message), ( (n1 := TRue) (n2 := TRue) m1) #  ((n1 := TRue) (n2 := TRue) m1') ->  ( (n1 := TRue) (n2 := FAlse) m2) #
 ( (n1 := TRue) (n2 := FAlse) m2') -> ((n1 := FAlse) m2) #  ((n1 := FAlse) m2') -> (if_then_else_M (Bvar n1) (if_then_else_M (Bvar n2) m1 m2) m2) #  (if_then_else_M (Bvar n1) (if_then_else_M (Bvar n2) m1' m2') m2').
 Proof. intros.  rewrite IFEVAL_M with (t1:= m1) (t2:= m2). rewrite IFEVAL_M with (t2:= m2).
simpl. rewrite IFEVAL_M with (t1:= m1') (t2:= m2'). rewrite IFEVAL_M with (t2:= m2').
simpl. rewrite H; rewrite H0 ; rewrite H1. reflexivity. Qed.

Axiom sub_invar: forall (t:message)  (b:Bool), (subbol_msg' b b t) # t. 
Axiom sub_in_sub: forall (b1 b2 b3 b4:Bool) (t:message), (**(occbol_in_msg b1 t = false) ->**) (subbol_msg' b1 b2 (subbol_msg' b3 b4 t)) # (subbol_msg' b3 (subbol_bol' b1 b2 b4) t).
Axiom dist_sesns_neq: forall (n1 n2:nat), (beq_nat n1 n2) =false  ->  (EQ_M (i n1) (i n2)) ##  FAlse.

Theorem dist_sesns_false: forall (n1 n2:nat),  (beq_nat n1 n2 = false) ->  (EQ_M (Mvar 1) (i n1)) & (EQ_M (Mvar 1) (i n2)) ## FAlse. 
Proof.  intros. 
unfold andB.
pose proof( EQ_BRmsg_msg''  (Mvar 1) (Mvar 1)  (i n1)    (EQ_M (Mvar 1) (i n2))  FAlse).
simpl in H0.
rewrite H0. 
apply dist_sesns_neq in H.
rewrite H. 
rewrite IFSAME_B. 
 reflexivity. 
Qed.

Theorem dist_sesns_false' : forall (n1 n2:nat) (x:message) , (beq_nat n1 n2 = false) ->  (EQ_M x (i n1)) & (EQ_M x (i n2)) ## FAlse .
Proof . 
intros. 
apply dist_sesns_false in H.
apply Forall_ELM_EVAL_B1 with (n:= 1) (b:= x) in H. simpl in H. assumption. Qed.

Theorem IFEVAL_M'': forall (n1 n2: nat) ( t1 t2:message), (beq_nat n1 n2 = false) -> (if_then_else_M  (EQ_M (Mvar 1) (i n1)) t1 t2) # (if_then_else_M  (EQ_M (Mvar 1) (i n1)) (subbol_msg' (EQ_M (Mvar 1) (i n2)) FAlse t1) t2).
Proof. 
intros.
apply dist_sesns_false in H.  
assert( (if_then_else_M (EQ_M (Mvar 1) (i n1)) t1 t2) #  (if_then_else_M (EQ_M (Mvar 1) (i n1)) (subbol_msg' (EQ_M (Mvar 1) (i n2)) (EQ_M (Mvar 1) (i n2)) t1) t2)).
rewrite sub_invar with(b:= (EQ_M (Mvar 1) (i n2))) (t:= t1). reflexivity.
assert( (EQ_M (Mvar 1) (i n2))  ##  (EQ_M (Mvar 1) (i n2)) & TRue).
simpl. unfold andB. rewrite IFTFb. reflexivity.
rewrite H1 in H0 at 2.
assert((if_then_else_M (EQ_M (Mvar 1) (i n1)) 
            (subbol_msg' (EQ_M (Mvar 1) (i n2))
               (EQ_M (Mvar 1) (i n2)) & (TRue) t1) t2) # (if_then_else_M (EQ_M (Mvar 1) (i n1))
            (subbol_msg' (EQ_M (Mvar 1) (i n2))
               (EQ_M (Mvar 1) (i n2)) & (EQ_M (Mvar 1) (i n1))  t1)  t2)).
 rewrite IFEVAL_M' with (t1:=  (subbol_msg' (EQ_M (Mvar 1) (i n2))
           (EQ_M (Mvar 1) (i n2)) & (EQ_M (Mvar 1) (i n1)) t1)).
rewrite IFEVAL_M'.
simpl. 
assert( (subbol_msg' (EQ_M (Mvar 1) (i n1)) TRue
         (subbol_msg' (EQ_M (Mvar 1) (i n2)) (EQ_M (Mvar 1) (i n2)) & (TRue)
            t1)) # (subbol_msg' (EQ_M (Mvar 1) (i n1)) TRue
           (subbol_msg' (EQ_M (Mvar 1) (i n2))
              (EQ_M (Mvar 1) (i n2)) & (EQ_M (Mvar 1) (i n1)) t1))).
repeat rewrite sub_in_sub. 

simpl.  rewrite <- beq_nat_refl. 
SearchAbout beq_nat.
rewrite <- Nat.eqb_sym.
destruct beq_nat. reflexivity.  reflexivity. 
rewrite H2. reflexivity.
rewrite H2 in H0.
rewrite andB_comm in H.
rewrite H in H0.
assumption. 
Qed.
Axiom IFMORPH_M2':  forall  ( b b1 b2 : Bool) (y z : message),
      (if_then_else_M (if_then_else_B b b1 b2) y z)
      # (if_then_else_M b (if_then_else_M b1 y z)
           (if_then_else_M b2 y z)).
Axiom IFEVAL_M''': forall (n1 n2: nat) (x t1 t2:message), beq_nat n1 n2 = false -> (if_then_else_M  (EQ_M x (i n1)) t1 t2) # (if_then_else_M  (EQ_M x (i n1)) (subbol_msg' (EQ_M x (i n2)) FAlse t1) t2).

Axiom andB_elm'':  forall (b1 b2 : Bool) (x y : message),
        (if_then_else_M (if_then_else_B b1 b2 FAlse) x y)
       # (if_then_else_M b1 (if_then_else_M b2 x y) y).
   
(** Some tactics defined here *)

Ltac redg := try rewrite IFTRUE_M ; try rewrite IFFALSE_M ; try rewrite IFSAME_M ;try rewrite IFTRUE_B ; try rewrite IFFALSE_B ; try rewrite IFSAME_B; try rewrite IFTFb.

Ltac red_in H:= try rewrite IFTRUE_M in H; try rewrite IFFALSE_M in H; try rewrite IFSAME_M in H;try rewrite IFTRUE_B in H; try rewrite IFFALSE_B in H; try rewrite IFSAME_B in H; try rewrite IFTFb in H.

(************rewrite hypothesis************)

Ltac rew_clear H := rewrite H ; simpl; clear H.
Ltac rew_clear_in H H1:= rewrite H in H1; simpl in  H1 ;clear H .

(*****************************Forall elimination ***************************)

Ltac fall_elm_in n1 b1 H := try apply Forall_ELM_EVAL_B with (n:= n1) (b:= b1) in H;  try apply Forall_ELM_EVAL_M with (n:= n1) (x:= b1) in H; simpl in H; try rewrite H.

Ltac fall_elm n1 b1  :=  try apply Forall_ELM_EVAL_B with (n:= n1) (b:= b1) ;  try apply Forall_ELM_EVAL_M with (n:= n1) (x:= b1) ;  simpl.

(*******************& elimination *******************)
Ltac andB_elm_msg n1 t1 t2  := pose proof( mor_eval_andB n1 t1 t2) ;
match goal with
| [H : ?X # ?Y |- _ ] =>    simpl in H ; match goal with | [H : ?X # ?Y |- _ ] =>   rewrite H; clear H end
         
 end.

Ltac andB_elm_msg_in n1 t1 t2 H1 := pose proof( mor_eval_andB n1 t1 t2) ;
match goal with
| [H : ?X # ?Y |- _ ] =>    simpl in H ; rewrite H in H1; clear H 
         
 end.

Ltac rew_andB_elm_msg :=
repeat match goal with 
|[H: _ |-  context [(if_then_else_M  ((Bvar ?n2) & ?P) ?X ?Y )] ] => andB_elm_msg n2 X Y 
end.

Ltac rew_andB_elm_in_msg H1 := 
repeat match goal with
 |[H: context [(if_then_else_M ((Bvar ?n2) & ?P) ?X ?Y )] |- _ ] =>  andB_elm_msg_in n2 X Y H1 end.

(***********************not sure if we require them*****)

Ltac andB_elm_bol n1 t1 t2  := pose proof( mor_eval_andB n1 t1 t2) ;
match goal with
| [H : ?X # ?Y |- _ ] =>    simpl in H ;  match goal with | [H : ?X # ?Y |- _ ] =>   rewrite H; clear H end
      end.

Ltac  andB_elm_bol_in n1 t1 t2 H1  := pose proof( mor_eval_andB n1 t1 t2) ;
match goal with
| [H : ?X # ?Y |- _ ] =>    simpl in H ;    rewrite H in H1; clear H 
        
 end.

Ltac rew_andB_elm_bol :=
repeat match goal with 
|[H: _ |-  context [(if_then_else_B ((Bvar ?n2) & ?P) ?X ?Y )] ] => andB_elm_bol  n2 X Y 
end.

Ltac rew_andB_elm_in_bol H1 := 
repeat match goal with
 |[H: context [(if_then_else_B ((Bvar ?n2) & ?P) ?X ?Y )] |- _ ] =>  andB_elm_bol_in n2 X Y H1 end.

(******************************************IFTF***********************************)

Ltac rew_IFTF b  := pose proof(IFTFb b); 
match goal with
| [H : _ |- ?X ## ?Y ] =>  rewrite H ; clear H; simpl
end.

Ltac rew_IFTF_in b H1  := pose proof(IFTFb b);
match goal with
  | [H : ?X ## ?Y |- _ ] =>   rewrite H in H1 ; clear H; simpl in H1
end.

Ltac rew_IFTF_all_in H1  := 
repeat match goal with 
|[ H : context [  (if_then_else_B ?X TRue FAlse)]   |- _ ] => rew_IFTF_in X H1 
end. 

Ltac rew_IFTF_all  := 
repeat match goal with 
|[ H : _ |-  context [ if_then_else_B ?X TRue FAlse ]  ] => rew_IFTF X 
end. 

(*************IFMORPH*****message_bool*******)

Ltac ifmor_msg_bol n1 b1 b2 t1 t2  := pose proof(IFMORPH_M2 n1 b1 b2 t1 t2);
match goal with
| [H : _ |-  ?X # ?Y ] =>    simpl in H ; match goal with | [H : ?X # ?Y |- _ ] =>   rewrite H; clear H end
       end.

Ltac ifmor_msg_bol_in n1 b1 b2 t1 t2 H1 := pose proof(IFMORPH_M2 n1 b1 b2 t1 t2);
match goal with
| [H : ?X # ?Y |- _ ] =>    simpl in H ; match goal with | [H : ?X # ?Y |- _ ] =>   rewrite H in H1; clear H end
       end.

Ltac rew_ifmor_msg_bol :=
repeat match goal with 
|[ H : _ |-  context [ if_then_else_M (if_then_else_B (Bvar ?n1) ?Y ?Z) ?P ?Q]  ] => ifmor_msg_bol n1 Y Z P Q
end. 

Ltac rew_ifmor_msg_bol_in H1 :=
repeat match goal with 
|[ H : context [ if_then_else_M (if_then_else_B (Bvar ?n1) ?Y ?Z) ?P ?Q]   |- _ ] => ifmor_msg_bol_in n1 Y Z P Q H1
end. 

(********************IFMRPH***********Bool_Bool_fst*****************)

Ltac ifmor_bol_bol_fst n1 b1 b2 b3 b4  := pose proof(IFMORPH_B2 n1 b1 b2 b3 b4);
match goal with
| [H :_ |-  ?X ## ?Y ] =>    simpl in H ; match goal with | [H : ?X ## ?Y |- _ ] =>   rewrite H; clear H end
         end.

Ltac ifmor_bol_bol_fst_in  n1 b1 b2 b3 b4 H1 := pose proof(IFMORPH_B2 n1 b1 b2 b3 b4);
match goal with
| [H : ?X ## ?Y |- _ ] =>    simpl in H ; match goal with | [H : ?X ## ?Y |- _ ] =>   rewrite H in H1; clear H end
  end.

Ltac rew_ifmor_bol_bol_fst :=
repeat match goal with 
|[ H : _ |-  context [ if_then_else_B (if_then_else_B (Bvar ?n1) ?Y ?Z) ?P ?Q]  ] =>  ifmor_bol_bol_fst n1 Y Z P Q
end. 

Ltac rew_ifmor_bol_bol_in_fst H1 :=
repeat match goal with 
|[ H : context [ if_then_else_B (if_then_else_B (Bvar ?n1) ?Y ?Z) ?P ?Q]   |- _ ] =>  ifmor_bol_bol_fst_in n1 Y Z P Q H1
end. 

(********************IFMRPH***********Bool_Bool_snd*****************)

Ltac ifmor_bol_bol_snd n1 n2 b1 b2 b3  := pose proof(IFMORPH_B1 n1 n2 b1 b2 b3 );
match goal with
| [H : _ |- ?X ## ?Y ] =>    simpl in H ; match goal with | [H : ?X ## ?Y |- _ ] =>   rewrite H; clear H end
         end.

Ltac ifmor_bol_bol_snd_in  n1 n2 b1 b2 b3  H1 := pose proof(IFMORPH_B1 n1 n2 b1 b2 b3 );
match goal with
| [H : ?X ## ?Y |- _ ] =>    simpl in H ; match goal with | [H : ?X ## ?Y |- _ ] =>   rewrite H in H1; clear H end
   end.

Ltac rew_ifmor_bol_bol_snd :=
repeat match goal with 
|[ H : _ |-  context [ if_then_else_B (Bvar ?n1) (if_then_else_B (Bvar ?n2) ?B1 ?B2) ?B3 ]  ] =>  ifmor_bol_bol_snd n1 n2 B1 B2 B3
end. 

Ltac rew_ifmor_bol_bol_in_snd H1 :=
repeat match goal with 
|[ H : context [ (if_then_else_B (Bvar ?n1) (if_then_else_B (Bvar ?n2) ?B1 ?B2) ?B3)]   |- _ ] =>  ifmor_bol_bol_snd_in n1 n2 B1 B2 B3 H1
end. 

(**************************************recent***************Testing************)
(**********************************tactics to apply if b is same on both sides**********)

Ltac aply_breq :=
match goal with
| [|- (if_then_else_M ?B ?X1 ?Y1) # (if_then_else_M ?B ?X2 ?Y2) ] =>  apply breq_msgeq'; simpl; redg; try reflexivity
end.

Ltac aply_breq_same :=
match goal with
| [|- (if_then_else_M ?B ?X ?Y1) # (if_then_else_M ?B ?X ?Y2) ] =>  apply breq_msgeq1'; simpl
end.

(********************************three sessions 1 2 3 *************************)
(******************tactics to make (to x) = j is false if (to x) = i is true where i <> j *********)
Ltac false_to_sesns n  := 
match goal with 
| [|- (if_then_else_M (EQ_M ?X (i ?N)) ?X1 ?Y1) #  (if_then_else_M (EQ_M ?X (i ?N)) ?X2 ?Y2) ] => assert (beq_nat N n =false) ; try reflexivity ;
match goal with 
| [H: beq_nat ?N ?N2 = false |- _ ] => 
  apply IFEVAL_M''' with (x:= X ) (n1:= N) (n2:= N2) (t1 := X1) (t2:= Y1) in H; rewrite H; clear H end; assert (beq_nat N n =false) ; try reflexivity ;
match goal with 
| [H: beq_nat ?N ?N2 = false |- _ ] => 
  apply IFEVAL_M''' with (x:= X ) (n1:= N) (n2:= N2) (t1 := X2) (t2:= Y2) in H; rewrite H; clear H end
end.

Ltac  false_to_sesns_all := try false_to_sesns 1; try false_to_sesns 2; try false_to_sesns 3.

(******************************************************************************)
(*************apply andB elm ****************)

Ltac aply_andB_elm := 
match goal with 
|[|- context[if_then_else_M (if_then_else_B ?B1 ?B2 FAlse) ?T1 ?T2 ] ] => rewrite andB_elm' with (b1:= B1) (b2:= B2) (x:= T1) (y:= T2)
end.


