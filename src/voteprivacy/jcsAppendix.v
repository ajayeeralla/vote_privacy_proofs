Require Export andbprops.

(** * Proposition 15 presented in Section B.1 in the Appendix *)
(** ** Unfold & *)
Proposition Prop_15_1: forall n1 n2 n3 n4, n2 <> n1 -> (If (Bvar n1) & (Bvar n2) then (Mvar n3) else (Mvar n4)) # (If (Bvar n1) then (If (Bvar n2) then (Mvar n3) else (Mvar n4)) else (Mvar n4)).
Proof. intros. unfold andB.
       rewrite <- IFSAME_M with (b:= (Bvar n1)) at 1.
       rewrite IFEVAL_M.
simpl.
rewrite <- beq_nat_refl. repeat rewrite IFTRUE_B, IFFALSE_B.
rewrite IFFALSE_M.
       apply beq_nat_false_iff in H. rewrite H. reflexivity. Qed.

(** ** Swapping Branches *)
(** TODO:XXX *)

(** ** Commutativity *)
Proposition Prop_15_3: forall n1 n2 , ( (Bvar n1) & (Bvar n2))  ## ( (Bvar n2) & (Bvar n1)).
Proof. intros. unfold andB.  rewrite <- IFTF with (n:= n2) at 1 . 
rewrite IFMORPH_B1 with (n1:= n2) (n2:=n1). rewrite IFTF with (n:= n1). rewrite IFSAME_B. reflexivity. Qed.

(** ** Associativity *)
Proposition Prop_15_4 : forall n1 n2 n3, (Bvar n1) & ((Bvar n2) & (Bvar n3)) ##( ((Bvar n1) & (Bvar n2)) & (Bvar n3)).

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

(** ** andB_false_r *)
Proposition Prop_15_5:  forall b:Bool, (b & FAlse) ## FAlse.
Proof. intros.  unfold andB. apply IFSAME_B. Qed.

(** ** andB_true_r *)
Proposition Prop_15_6: forall b:Bool, b & TRue ## b.
Proof.  intros. unfold andB. 
pose proof (IFTF 1).
apply Forall_ELM_EVAL_B with (n :=1)(b:=b) in H.
simpl in H.
apply H.  Qed.

(** ** x & not(x) = x *)
Proposition Prop_15_7: forall n, (Bvar n) & (notb (Bvar n)) ## FAlse.
Proof. intros. unfold  andB.
unfold notb. rewrite IFMORPH_B1. 
       rewrite IFIDEMP_B. rewrite IFSAME_B. reflexivity. Qed.

(** ** notB_involutive *)
Proposition Prop_15_8 : forall n, ! (! (Bvar n)) ## (Bvar n).
Proof.  intros. unfold notb. 
 rewrite IFMORPH_B2. rewrite IFFALSE_B. rewrite IFTRUE_B.
 rewrite IFTF. reflexivity. Qed.
