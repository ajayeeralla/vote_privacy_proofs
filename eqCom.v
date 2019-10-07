(************************************************************************)
(* Copyright (c) 2015-2019, Ajay Kumar Eeralla                          *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(************************************************************************)    

Require Export eqBranch.
Require Import Omega.
(** This library defines a theorem that states, 

[forall x y, (eqm x y) = (eqm y x)]. *)

Theorem Example14_M: forall (n1 m1 : nat),  (eqm (Mvar n1) (Mvar m1) ) ##  (eqm (Mvar m1) (Mvar n1)).
Proof.
intros . 
assert(H : (Bvar 1) ## (IF (Bvar 1) then TRue else FAlse)).
rewrite IFTF with (n:=1). reflexivity.
apply Forall_ELM_EVAL_B with (n:=1)(b:= (eqm (Mvar n1) (Mvar m1))) in H .
simpl in H.
assert ( Eq: (eqm (Mvar n1) (Mvar n1)) ## TRue).
apply EQmsg.
reflexivity.
rewrite <- Eq in H.
assert(H2: (IF (eqm (Mvar n1) (Mvar m1)) then [[ (n1+m1+1):= (Mvar n1)]](eqm (Mvar (n1+m1 +1)) (Mvar n1)) else
      FAlse) ## (IF (eqm (Mvar n1) (Mvar m1)) then [[ (n1+m1+1):= (Mvar m1)]](eqm (Mvar (n1+m1+1)) (Mvar n1))
      else FAlse)).
apply eqbrmsg_bol with (n1:= n1)(n2:= m1)(n3:=(n1+m1+1))(b1:= (eqm (Mvar (n1+m1+1)) (Mvar n1))) (b2:= FAlse).
simpl in H2.
assert(H4: n1<> n1+m1+1).
omega.
assert (H3: beq_nat (n1+m1+1) n1  = false).
SearchAbout beq_nat.  
apply beq_nat_false_iff  with (x:=n1)(y:=n1+m1+1) in H4; auto.
rewrite Nat.eqb_sym; auto.
rewrite H3 in H2.
simpl. 
rewrite <- beq_nat_refl in H2.
rewrite H2 in H.
assert(H5 :  (Bvar 1) ##  (IF (Bvar 1) then TRue else FAlse)).
rewrite IFTF with (n:=1). reflexivity.
apply Forall_ELM_EVAL_B2 with (n:=1)(b:= (eqm (Mvar m1) (Mvar n1))) in H5 .
simpl in H5.
rewrite H5 in H.
assert(H6:(IF (Bvar 1) then (IF (Bvar 2) then TRue else FAlse) else FAlse) ## (IF (Bvar 2) then (IF (Bvar 1) then TRue else FAlse) else (IF (Bvar 1) then FAlse else FAlse))).
rewrite <- IFMORPH_B1 with (n2 :=1)(b:=TRue ) (b1:=FAlse)(b2:= FAlse).
reflexivity.
apply Forall_ELM_EVAL_B with (n:=1)(b:= (eqm (Mvar n1) (Mvar m1))) in H6 .
simpl in H6.
apply Forall_ELM_EVAL_B with (n:=2)(b:= (eqm (Mvar m1) (Mvar n1))) in H6 .
simpl in H6.
pose proof(IFSAME_B).
rewrite IFSAME_B in H6.
rewrite H6 in H.
assert(H7 : (Bvar 1) ## (IF (Bvar 1) then TRue else FAlse)).
rewrite IFTF with (n:=1). reflexivity.
apply Forall_ELM_EVAL_B2 with (n:=1)(b:= (eqm (Mvar n1) (Mvar m1))) in H7 .
simpl in H7.
rewrite <- H7 in H.
assert(H8:  (IF (eqm (Mvar m1) (Mvar n1)) then [[ (n1+m1+1):= (Mvar m1)]](eqm (Mvar (n1+m1 +1)) (Mvar m1)) else
      FAlse) ##  (IF (eqm (Mvar m1) (Mvar n1)) then [[ (n1+m1+1):= (Mvar n1)]](eqm (Mvar (n1+m1+1)) (Mvar m1)) else
      FAlse)).
apply eqbrmsg_bol with (n1:= m1)(n2:= n1)(n3:=(n1+m1+1))(b1:= (eqm (Mvar (n1+m1+1)) (Mvar m1))) (b2:= FAlse).
simpl in H8.
assert(H9: m1<> n1+m1+1).
omega.
assert (H10: beq_nat (n1+m1+1)  m1 = false).
apply beq_nat_false_iff  with (x:=m1)(y:=n1+m1+1) in H9. rewrite Nat.eqb_sym; auto.
rewrite H10 in H8.
simpl in H8.
rewrite <- beq_nat_refl in H8.
rewrite <- H8 in H.
assert(H11:( eqm (Mvar m1) (Mvar m1)) ## TRue).
apply  EQmsg with (x:= (Mvar m1)) (y:= (Mvar m1)).
reflexivity.
rewrite H11 in H.
assert(H12 : (Bvar 1) ## (IF (Bvar 1) then TRue else FAlse)).
rewrite IFTF with (n:=1).
reflexivity.
apply Forall_ELM_EVAL_B2 with (n:=1)(b := (eqm (Mvar m1)(Mvar n1))) in H12.
simpl in H12.
rewrite <- H12 in H.
apply H.
Qed.

Axiom Example14_M': forall (m1 m2: message),  (m1 #? m2) ##  (m2 #? m1).
(*Proof. intros. pose proof(Example14_M 0 1).
       apply Forall_ELM_EVAL_B1 with (n:= 0) (b:=m1) in H.    simpl in H.
       apply Forall_ELM_EVAL_B1 with (n:= 1) (b:=m2) in H. simpl in H.*)