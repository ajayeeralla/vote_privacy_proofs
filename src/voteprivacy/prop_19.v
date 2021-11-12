Require Export prop_17.

Definition phi0 := [msg A, msg B, msg M, msg C1, msg C2, msg C3, msg ONE, msg TWO, msg THREE, msg (vk 0), msg (vk 1), msg (pke 2)].

(** STEP:1 *)
Definition vcheck (v:message) :=  (v #? C1) or (v#?C2) or (v#?C3).
Definition x1:= f (toListm phi0).
Definition pk:= (pubkey x1).
(* Axiom vote_len_reg : forall t, (|V0 t| #? |V1 t|) ## TRue. *)
(** * Phase 1:Authentication *)
(** nA = 0, nB = 1, nM = 2 *)
(*Eval compute in ssk. *)
Definition v (n:nat) := match n with
                        | 0 => V0 (x1)
                        | 1 => V1 (x1)
                        | _ => O
                        end.

Axiom ext_ifeval: forall b1 b2 b3 x y, (IF b1 & (!b2)&(!b3) then x else y) ## (IF b1 & (!b2)&(!b3) then (subbol_bol' b1 TRue (subbol_bol' b2 FAlse (subbol_bol' b3 FAlse x))) else  (subbol_bol' b1 FAlse (subbol_bol' b2 TRue (subbol_bol' b3 TRue y)))).
Axiom eqbrmsg_msg'' :forall ( m m1 m2:message) (b1 b2: Bool) ,  (IF (m1 #? m2) then (submsg_bol' m m1 b1) else b2) ##  (IF (eqm m1 m2) then (submsg_bol' m m2 b1) else b2).

Ltac aply_eqbr :=
match goal with
| [|-  context [IF (?X #? ?Y) then ?B1 else ?B2] ] => pose proof (eqbrmsg_msg'' X X Y B1 B2)
end.
(** Using ext_comp_hid **)
(*Eval compute in (v 0). *)
Theorem vote_len_eql: (IF (vcheck (v 0)) & (vcheck (v 1)) then |(v 0)|#? |(v 1)| else TRue) ## TRue.
Proof. unfold vcheck.
rewrite <- IFSAME_B with (b:= ((v 0) #? C1)).
rewrite IFEVAL_B'.
simpl.
repeat redg.
aply_eqbr.
simpl in H.
rewrite H.
clear H.
rewrite <- IFSAME_B with (b:= ((v 1) #? C1)).
rewrite IFEVAL_B'.
simpl.
repeat redg.
aply_eqbr.
simpl in H.
repeat red_in H.
rewrite eqmeql in H. repeat red_in H.
rewrite H; clear H.
rewrite <- IFSAME_B with (b:= ((v 0) #? C2)).
rewrite IFEVAL_B' ; repeat redg.
simpl.
repeat redg.
aply_eqbr.
simpl in H.
pose proof(candEql1).
Axiom Example14_M': forall m1 m2, (m1 #? m2) ## (m2 #? m1).

rewrite Example14_M' in H0.
rewrite H0 in H.
repeat red_in H. rewrite H.
rewrite <- IFSAME_B with (b:= ((v 1) #? C2)).
rewrite IFEVAL_B'.
simpl.
repeat redg.
aply_eqbr.
simpl in H1.
repeat rewrite eqmeql in H1.
repeat red_in H1.
rewrite Example14_M' in H0.
rewrite H0 in H1; repeat red_in H1.
rewrite H1. clear H1. clear H.
rewrite <- IFSAME_B with (b:= ((v 0) #? C3)).
rewrite IFEVAL_B'.
simpl.
repeat redg.
aply_eqbr.
simpl in H.
repeat red_in H.
pose proof (candEql2).
pose proof (candEql3).
rewrite Example14_M' in H1.

repeat rewrite H1 in H.
rewrite Example14_M' in H2.
rewrite H2 in H. repeat red_in H.
rewrite H.
clear H.
rewrite <- IFSAME_B with (b:= ((v 1) #? C3)).
rewrite IFEVAL_B'.
simpl.
repeat redg.
aply_eqbr.
simpl in H.
rewrite Example14_M' in H2.
repeat rewrite H2 in H.
rewrite Example14_M' in H0.
repeat rewrite H0 in H.
rewrite Example14_M' in H1.
repeat rewrite H1 in H.
repeat rewrite eqmeql in H.
repeat red_in H. rewrite H.
reflexivity.
Qed.