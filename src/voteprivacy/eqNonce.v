(************************************************************************)
(* Copyright (c) 2015-2019, Ajay Kumar Eeralla                          *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(************************************************************************)

Require Export eqCom.
Require Import Coq.Bool.Bool.
Require Export Coq.Init.Peano.
(** This library defines a theorem that states,
<<
n1<> n2 => EQ ( (nonce n1) , <(nonce n1),(nonce n2)>)= false.
>>
 *)

Theorem Example_15 : (nonce 1)#?((nonce 1),(nonce 2)) ## FAlse.
Proof.
assert(H1: (IF (Bvar 0) then TRue else FAlse) ## (Bvar 0)).
apply IFTF.
apply Forall_ELM_EVAL_B with (n:= 0) (b:= (eqm (nonce 1)  (pair (nonce 1) (nonce 2)))) in H1.
simpl in H1.
rewrite <- H1.
assert (Eq_check: (eqm (nonce 2) (pi2 ( pair (nonce 1)  (nonce 2)  ))) ## TRue).
rewrite proj2.
apply EQmsg.
reflexivity.
rewrite <- Eq_check.
assert( J: (IF (eqm (Mvar 1) (Mvar 2)) then [[3:= Mvar 1]](eqm (nonce 2) (pi2  (Mvar 3))) else FAlse) ## (IF (eqm (Mvar 1) (Mvar 2)) then [[3:= Mvar 2]](eqm (nonce 2) (pi2(Mvar 3))) else FAlse)).
apply eqbrmsg_bol with (n1:=1)(n2:=2) (n3:= 3)(b1 :=  (eqm (nonce 2)( pi2 (Mvar 3)))) (b2 := FAlse).
simpl in J.
apply Forall_ELM_EVAL_B1 with (n:=1)(b:=(nonce 1)) in J.
simpl in J.
apply Forall_ELM_EVAL_B1 with (n:=2)(b:=(pair (nonce 1) (nonce 2))) in J.
simpl in J.
apply Forall_ELM_EVAL_B1 with (n:=3)(b:=(nonce 2)) in J.
simpl in J.
rewrite <- J.
assert (Fr: (closMsg (pi2 (nonce 1)) = true)/\ Fresh (cons 2 nil) [msg (pi2 (nonce 1))] = true).
split.
simpl. reflexivity.
simpl.
reflexivity.
apply FRESHNEQ in Fr.
apply Example10_B with (x := (eqm (nonce 2)(pi2 (nonce 1)))) (F:=  FAlse)(z:= TRue) in Fr.
unfold const in Fr.
rewrite Fr.
apply IFSAME_B.
Qed.

Theorem dist_notocc : forall (n1 n2 :nat), (beq_nat n1 n2 ) = false ->  (occur_name_msg n2 ((pi2 (nonce n1)))) = false.
Proof. intros.
-induction n1.
  + induction n2. simpl. inversion H.  simpl. reflexivity.
 + induction n2. simpl. reflexivity. simpl. simpl in H. rewrite H. reflexivity.

Qed.

Theorem Example_15B :  forall (n1 n2:nat), (beq_nat n1 n2) = false -> (nonce n1)#?((nonce n1), (nonce n2)) ## FAlse.
Proof.
intros n1 n2 distinct.
assert(H1: (IF (Bvar 0) then TRue else FAlse) ## (Bvar 0)).
apply IFTF.
apply Forall_ELM_EVAL_B with (n:= 0) (b:= (eqm (nonce n1) (pair (nonce n1) (nonce n2)))) in H1.
simpl in H1.
rewrite <- H1.
assert (Eq_check: (eqm (nonce n2) (pi2 ( pair (nonce n1)  (nonce n2)  ))) ## TRue).
rewrite proj2.
apply EQmsg.
reflexivity.
rewrite <- Eq_check.
simpl.
assert( J: (IF (eqm (Mvar 1) (Mvar 2)) then [[3:= Mvar 1]](eqm (nonce n2) (pi2  (Mvar 3))) else FAlse) ## (IF (eqm (Mvar 1) (Mvar 2)) then [[3:= Mvar 2]](eqm (nonce n2) (pi2(Mvar 3))) else FAlse)).
apply eqbrmsg_bol with (n1:=1)(n2:=2) (n3:= 3)(b1 :=  ( eqm (nonce n2)( pi2 (Mvar 3)))) (b2 := FAlse).
simpl in J.
apply Forall_ELM_EVAL_B1 with (n:=1)(b:=(nonce n1)) in J.
simpl in J.
apply Forall_ELM_EVAL_B1 with (n:=2)(b:=(pair (nonce n1) (nonce n2))) in J.
simpl in J.
apply Forall_ELM_EVAL_B1 with (n:=3)(b:=(nonce n2)) in J.
simpl in J.
rewrite <- J.
assert (Fr: (closMsg (pi2 (nonce n1)) = true)/\ Fresh (cons n2 nil) [msg (pi2 (nonce n1))] = true).
split. reflexivity.
unfold Fresh.
apply andb_true_iff.
split.
2: { simpl.
    rewrite distinct.
    reflexivity.
}
unfold noDupNlist. simpl. rewrite <- beq_nat_refl. reflexivity.
apply FRESHNEQ in Fr.
apply Example10_B with (x := (eqm (nonce n2)(pi2 (nonce n1)))) (F:=  FAlse)(z:= TRue) in Fr.
unfold const in Fr.
rewrite Fr.
apply IFSAME_B.
Qed.

