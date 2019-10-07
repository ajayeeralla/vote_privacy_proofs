(************************************************************************)
(* Copyright (c) 2017-2018, Ajay Kumar Eeralla <ae266@mail.missouri.edu>*)     
(************************************************************************)
 
Require Export axioms.
Open Scope msg_scope.
 Section andb_props. 
Axiom IFTF: forall (n: nat), (IF (Bvar n) then TRue else FAlse) ## (Bvar n).
Theorem IFMORPH_B1: forall ( b b1 b2 : Bool) (n1 n2:nat) ,
 (IF (Bvar n2) then (IF (Bvar n1) then b else b1) else b2)  ## (IF (Bvar n1) then (IF (Bvar n2) then b else b2) else (IF (Bvar n2) then b1 else b2)).
Proof.
intros.
rewrite <- IFSAME_B with (b:= (Bvar n1)) (b1:= (IF (Bvar n2) then (IF (Bvar n1) then b else b1) else b2)).
rewrite IFEVAL_B.
simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_B.
rewrite IFFALSE_B.
rewrite IFEVAL_B with (n:=n1)(b1:= (IF (Bvar n2) then b else b2))(b2:= (IF (Bvar n2) then b1 else b2)).
simpl.
reflexivity.
Qed.


Theorem IFMORPH_B2: forall (n:nat)(b1 b2 b3 b4 : Bool) , 
(IF (IF (Bvar n) then b1 else b2) then b3 else b4) ## (IF (Bvar n) then (IF b1 then b3 else b4) else (IF b2 then b3 else b4)).
Proof.
intros.
pose proof (IFSAME_B).
rewrite <- IFSAME_B with (b:= (Bvar n)) (b1:= (IF (IF (Bvar n) then b1 else b2) then b3 else b4)).
pose proof(IFEVAL_B).
rewrite IFEVAL_B.
simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_B.
rewrite IFFALSE_B.
rewrite IFEVAL_B with (b1 := (IF b1 then b3 else b4))(b2:= (IF b2 then b3 else b4)).
simpl.
reflexivity.
Qed.

Theorem IFIDEMP_B : forall (n: nat)(b1 b2 b3 b4 : Bool), (IF (Bvar n) then (IF (Bvar n) then b1 else b2) else (IF (Bvar n) then b3 else b4)) ## (IF (Bvar n) then b1 else b4).
Proof.
 intros n b1 b2 b3 b4.
rewrite IFEVAL_B with (b1:= IF (Bvar n) then b1 else b2)(b2 := (IF (Bvar n) then b3 else b4)) .
simpl.
rewrite <-beq_nat_refl.
rewrite IFTRUE_B.
rewrite IFFALSE_B.
rewrite IFEVAL_B with(b2:=b4).
reflexivity.               
Qed.
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

Lemma andB_FAlse_intro2 : forall b1 b2:Bool, b2 ## FAlse -> b1 & b2  ## FAlse.
Proof. intros. unfold andB. rewrite H. apply IFSAME_B. Qed.

Lemma andB_FAlse_r :  forall b:Bool, (b & FAlse) ## FAlse.
Proof. intros.  unfold andB. apply IFSAME_B. Qed.

Lemma andB_FAlse_l : forall b: Bool, (FAlse & b) ## FAlse.
Proof. intros. unfold andB. apply IFFALSE_B. Qed.

Lemma andB_diag : forall n, ((Bvar n) & (Bvar n) ) ## (Bvar n).
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
Axiom andB_prop : forall a b:Bool, (andB a b) ## TRue -> (a ## TRue) /\ (b ## TRue).

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

Lemma notB_involutive : forall n, ! (! (Bvar n)) ## (Bvar n).

Proof.  intros. unfold notb. 

 rewrite IFMORPH_B2. rewrite IFFALSE_B. rewrite IFTRUE_B.
 rewrite IFTF. reflexivity. Qed.

Theorem notB_inv_gen : forall b, ! (! b) ## b.
Proof. intros. unfold notb. pose proof(IFMORPH_B2 0 FAlse TRue FAlse TRue).
apply Forall_ELM_EVAL_B with (n:=0) (b:=b) in H. simpl in H.
rewrite IFFALSE_B in H.  rewrite IFTRUE_B in H.
rewrite H. pose proof(IFTF 0).
apply Forall_ELM_EVAL_B with (n:=0) (b:=b) in H0. simpl in H0.
rewrite H0. reflexivity.
Qed.


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

Theorem b1_notb2 : forall (n1 : nat) , (Bvar n1) & (notb (Bvar (n1+1))) ##
(IF (Bvar (n1+1)) then FAlse else (Bvar n1)) .

Proof.
 intros.
unfold notb, andB.
rewrite <- IFSAME_B with (b:= (Bvar (n1+1))) (b1:= (IF (Bvar n1) then (IF (Bvar (n1 + 1)) then FAlse else TRue) else FAlse)).
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
End andb_props.


