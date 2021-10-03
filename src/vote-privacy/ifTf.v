Require Export andbprops.

(** * [IFTF] *)
(** The theorem states that for any [b], [ if b then true else false = b ]. Notice that we use [#] (resp. [##]) for [message] (resp. [Bool]) in lieu of [=]. *)

Theorem IFTF:  forall (n:nat),  (IF (Bvar n) then TRue else FAlse) ## (Bvar n).
Proof.
intros.
rewrite <- (IFSAME_B (Bvar n) (Bvar n)) at 2.
rewrite -> IFEVAL_B with (b1 := (Bvar n)).
simpl.
rewrite <- beq_nat_refl.
reflexivity.
Qed. 

Theorem IFTFb : forall (b:Bool),  (IF b then TRue else FAlse) ## b.
Proof. intros;pose proof(IFTF 0); apply Forall_ELM_EVAL_B with (n:=0) (b:=b) in H; simpl in H; auto. Qed.
