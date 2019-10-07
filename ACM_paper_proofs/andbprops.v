(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                     Rohit Chadha <chadhar@missouri.edu>              *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)

Load "ex5_4_IFMORPH".
(** * [andB] properties *)

(** This library defines some of the properties of [andB]. *)

(** [FAlse] if one of them is [FAlse]. *)
Lemma andB_FAlse_intro1 : forall b1 b2 : Bool, b1 ## FAlse -> b1 & b2 ## FAlse.
Proof.
intros.
unfold andB .
rewrite H.
apply IFFALSE_B. 
Qed.

Lemma andB_FAlse_intro2 : forall b1 b2:Bool, b2 ## FAlse -> b1 & b2 ## FAlse.
Proof. intros. unfold andB. rewrite H. apply IFSAME_B. Qed.

Lemma andB_FAlse_r :  forall b:Bool, b & FAlse ## FAlse.
Proof. intros.  unfold andB. apply IFSAME_B. Qed.

Lemma andB_FAlse_l : forall b: Bool, FAlse & b ## FAlse.
Proof. intros. unfold andB. apply IFFALSE_B. Qed.

Lemma andB_diag : forall n, (Bvar n) & (Bvar n) ## (Bvar n).
Proof.  intros. unfold andB. rewrite IFEVAL_B. simpl. 
rewrite <- beq_nat_refl.
 rewrite IFTF.
reflexivity.
Qed.

(** Invariant under [TRue]. *)

Lemma andB_TRue_r : forall b:Bool, b & TRue ## b.

Proof.  intros. unfold andB.
pose proof (IFTF 1).
apply Forall_ELM_EVAL_B with (n :=1)(b:=b) in H.
simpl in H.
apply H.  Qed.  

Lemma andB_TRue_l : forall b:Bool,  TRue & b ## b.

Proof.  intros. unfold andB.
apply IFTRUE_B.
   Qed.           

Lemma andB_notb_r : forall n, (Bvar n) & (notb (Bvar n)) ## FAlse.

Proof. intros. unfold andB .  unfold notb.  rewrite IFEVAL_B. simpl. rewrite <- beq_nat_refl. 
rewrite IFTRUE_B. rewrite IFSAME_B. reflexivity. Qed.

(** [andB] is commutative. *)

Lemma andB_comm1: forall n1 n2 , ( (Bvar n1) & (Bvar n2))  ## ( (Bvar n2) & (Bvar n1)).

Proof. intros. unfold andB.  rewrite <- IFTF with (n:= n2) at 1 . 

rewrite IFMORPH_B1 with (n1:= n2) (n2:=n1). rewrite IFTF with (n:= n1). rewrite IFSAME_B. reflexivity. Qed.

Axiom andB_comm: forall (b1 b2: Bool), (b1 & b2) ## (b2 & b1).

(** [andB] is associative *)

Lemma andB_assoc1 : forall n1 n2 n3, (Bvar n1) & ((Bvar n2) & (Bvar n3)) ##( ((Bvar n1) & (Bvar n2)) & (Bvar n3)).

Proof. intros. unfold andB.
pose proof(andB_comm1).
unfold andB in H.
pose proof (IFMORPH_B1).
 rewrite IFMORPH_B1 with (n1:= n2) (n2:= n1).
rewrite H with (n1:=n1) (n2:= n2).
rewrite IFMORPH_B2.
rewrite IFSAME_B.
rewrite IFFALSE_B.
reflexivity.
Qed.

Axiom andB_assoc: forall (b1 b2 b3: Bool), (b1 & b2) & b3 ## b1 & (b2 & b3).
Lemma andB_prop : forall a b:Bool, (andB a b) ## TRue -> (a ## TRue) /\ (b ## TRue).
Proof. 
intros.
unfold andB in H.
pose proof(IFSAME_B b (if_then_else_B a b FAlse)).
Admitted.
Lemma andB_TRue_intro : forall b1 b2:Bool, b1 ## TRue /\ b2 ## TRue -> (andB b1 b2) ## TRue.
Proof. intros.
inversion H.
unfold andB.
rewrite H0.
rewrite IFTRUE_B.
assumption.
Qed.

Lemma andB_TRue_iff :  forall n1 n2, (Bvar n1) & (Bvar n2) ## TRue <-> (Bvar n1) ## TRue /\ (Bvar n2) ## TRue.
Proof. split.
apply andB_prop.
apply andB_TRue_intro.
Qed.

(** [notb] properties *)

Lemma notB_involutive : forall n, (notb (notb (Bvar n))) ## (Bvar n).

Proof. intros. unfold notb. 

 rewrite IFMORPH_B2. rewrite IFFALSE_B. rewrite IFTRUE_B.
rewrite IFTF. reflexivity. Qed.


Lemma notB_TRue_iff : forall n, ( notb (Bvar n)) ## TRue <-> (Bvar n) ## FAlse.
Proof.
intros. split.
intros.
rewrite <- notB_involutive.
rewrite H.
unfold notb .
rewrite IFTRUE_B.
reflexivity.
intros.
rewrite H.
unfold notb.
rewrite IFFALSE_B.
reflexivity.
Qed.

Lemma notb_FAlse_iff : forall n, (notb (Bvar n)) ## FAlse <-> (Bvar n) ## TRue.

Proof. intros. split.

intros.  rewrite <- notB_involutive. rewrite H. unfold notb. rewrite IFFALSE_B.  reflexivity.

intros. rewrite H. unfold notb.

rewrite IFTRUE_B. reflexivity. Qed.


(** [andB] complement *)



Lemma and_notB_r : forall n, (Bvar n) & (notb (Bvar n)) ## FAlse.
Proof. intros. unfold  andB.
unfold notb. rewrite IFMORPH_B1. 
rewrite IFIDEMP_B. rewrite IFSAME_B. reflexivity. Qed.

Lemma and_notB_l : forall n, (notb (Bvar n)) & (Bvar n) ## FAlse.
Proof. intros. unfold  andB.
unfold notb. rewrite IFMORPH_B2. 
rewrite IFFALSE_B, IFTRUE_B.
rewrite IFEVAL_B.
simpl.
rewrite <- beq_nat_refl.
rewrite IFSAME_B.
reflexivity. Qed.

Theorem b1_notb2 : forall (n1 : nat) , (Bvar n1) &(notb (Bvar (n1+1))) ##
(if_then_else_B (Bvar (n1+1)) FAlse (Bvar n1)) .

Proof.
 intros.
unfold notb, andB.
rewrite <- IFSAME_B with (b:= (Bvar (n1+1))) (b1:= (if_then_else_B (Bvar n1) (if_then_else_B (Bvar (n1 + 1)) FAlse TRue) FAlse)).
rewrite IFEVAL_B with (n := (n1+1)).
 simpl.
rewrite <- beq_nat_refl.
rewrite IFFALSE_B.
rewrite IFTRUE_B.
rewrite IFSAME_B.
(*************)
assert(H: beq_nat n1 (n1 + 1) = false).
induction n1.
reflexivity. 
simpl.
assumption.
(************)
rewrite H.
rewrite IFTF.
reflexivity.
Qed.


