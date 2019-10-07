(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                     Rohit Chadha <chadhar@missouri.edu>              *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)
Load "ex7_6".

(** This library defines a theorem that states,
<< 
n1<> n2 => EQ ( (N n1) , <(N n1),(N n2)>)= false.
>>
 *)

Theorem Example_15 :    (EQ_M (N 1)   (pair (N 1)  (N 2) )) ## FAlse.
Proof.
assert(H1: (if_then_else_B (Bvar 0) TRue FAlse) ## (Bvar 0)).
apply IFTF.
apply Forall_ELM_EVAL_B with (n:= 0) (b:= (EQ_M (N 1)  (pair (N 1) (N 2)))) in H1.
simpl in H1.
rewrite <- H1.
assert (Eq_check: (EQ_M (N 2) (pi2 ( pair (N 1)  (N 2)  ))) ## TRue).
rewrite proj2.
apply EQmsg.
reflexivity.
rewrite <- Eq_check.
assert( J: (if_then_else_B (EQ_M (Mvar 1) (Mvar 2) ) [[3:= Mvar 1]](EQ_M (N 2) (pi2  (Mvar 3))) FAlse) ## (if_then_else_B  (EQ_M (Mvar 1) (Mvar 2)) [[3:= Mvar 2]](EQ_M (N 2) (pi2(Mvar 3))) FAlse)).
apply EQ_BRmsg_bol with (n1:=1)(n2:=2) (n3:= 3)(b1 :=  ( EQ_M (N 2)( pi2 (Mvar 3)))) (b2 := FAlse).
simpl in J.
apply Forall_ELM_EVAL_B1 with (n:=1)(b:=(N 1)) in J.
simpl in J. 
apply Forall_ELM_EVAL_B1 with (n:=2)(b:=(pair (N 1) (N 2))) in J.
simpl in J.
apply Forall_ELM_EVAL_B1 with (n:=3)(b:=(N 2)) in J.
simpl in J.
rewrite <- J.
assert (Fr: (clos_msg (pi2 (N 1)) = true)/\ Fresh [ 2] [msg (pi2 (N 1))] = true).
split.
simpl. reflexivity.
simpl.
reflexivity.
apply FRESHNEQ in Fr.
apply Example10_B with (x := (EQ_M (N 2)(pi2 (N 1)))) (F:=  FAlse)(z:= TRue) in Fr.
unfold const in Fr.
rewrite Fr.
apply IFSAME_B.
Qed.

Theorem dist_notocc : forall (n1 n2 :nat), (beq_nat n1 n2 ) = false ->  notoccur_os n2 (msg (pi2 (N n1))) = true.
Proof. intros.
-induction n1. 
  + induction n2. simpl. inversion H.  simpl. reflexivity.
 + induction n2. simpl. reflexivity. simpl. simpl in H. rewrite H. reflexivity.

Qed.

Theorem Example_15B :  forall (n1 n2:nat), (beq_nat n1 n2) = false -> (EQ_M (N n1)   (pair (N n1)  (N n2) )) ## FAlse.
Proof.
intros n1 n2 distinct.
assert(H1: (if_then_else_B (Bvar 0) TRue FAlse) ## (Bvar 0)).
apply IFTF.
apply Forall_ELM_EVAL_B with (n:= 0) (b:= (EQ_M (N n1)  (pair (N n1) (N n2)))) in H1.
simpl in H1.
rewrite <- H1.
assert (Eq_check: (EQ_M (N n2) (pi2 ( pair (N n1)  (N n2)  ))) ## TRue).
rewrite proj2.
apply EQmsg.
reflexivity.
rewrite <- Eq_check.
simpl.
assert( J: (if_then_else_B (EQ_M (Mvar 1) (Mvar 2) ) [[3:= Mvar 1]](EQ_M (N n2) (pi2  (Mvar 3))) FAlse) ## (if_then_else_B  (EQ_M (Mvar 1) (Mvar 2)) [[3:= Mvar 2]](EQ_M (N n2) (pi2(Mvar 3))) FAlse)).
apply EQ_BRmsg_bol with (n1:=1)(n2:=2) (n3:= 3)(b1 :=  ( EQ_M (N n2)( pi2 (Mvar 3)))) (b2 := FAlse).
simpl in J.
apply Forall_ELM_EVAL_B1 with (n:=1)(b:=(N n1)) in J.
simpl in J. 
apply Forall_ELM_EVAL_B1 with (n:=2)(b:=(pair (N n1) (N n2))) in J.
simpl in J.
apply Forall_ELM_EVAL_B1 with (n:=3)(b:=(N n2)) in J.
simpl in J.
rewrite <- J.
assert (Fr: (clos_msg (pi2 (N n1)) = true)/\ Fresh [ n2] [msg (pi2 (N n1))] = true).
split. reflexivity.
unfold Fresh. unfold notoccur_mylist. 
apply andb_true_iff with (b1:= notoccur_os n2 (msg (pi2 (N n1))))(b2:= true).
split. 
Focus 2. reflexivity. apply dist_notocc. apply distinct.
apply FRESHNEQ in Fr.
apply Example10_B with (x := (EQ_M (N n2)(pi2 (N n1)))) (F:=  FAlse)(z:= TRue) in Fr.
unfold const in Fr.
rewrite Fr.
apply IFSAME_B.
Qed.

