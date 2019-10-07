(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                     Rohit Chadha <chadhar@missouri.edu>              *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)
Load "ex7_5".

(** This library defines a theorem that states, 

[forall x y, (EQ_M x y) = (EQ_M y x)]. *)

Theorem Example14_M: forall (n1 m1 : nat),  (EQ_M (Mvar n1) (Mvar m1) ) ##  (EQ_M (Mvar m1) (Mvar n1)).
Proof.
intros . 
assert(H : (Bvar 1) ## (if_then_else_B (Bvar 1) TRue FAlse)).
rewrite IFTF with (n:=1). reflexivity.
apply Forall_ELM_EVAL_B with (n:=1)(b:= (EQ_M (Mvar n1) (Mvar m1))) in H .
simpl in H.
assert ( Eq: (EQ_M (Mvar n1) (Mvar n1)) ## TRue).
apply EQmsg.
reflexivity. 
rewrite <- Eq in H.
assert(H2: ( if_then_else_B (EQ_M (Mvar n1) (Mvar m1)) [[ (n1+m1+1):= (Mvar n1)]](EQ_M (Mvar (n1+m1 +1)) (Mvar n1))
      FAlse) ## (if_then_else_B (EQ_M (Mvar n1) (Mvar m1)) [[ (n1+m1+1):= (Mvar m1)]](EQ_M (Mvar (n1+m1+1)) (Mvar n1))
      FAlse)).
apply EQ_BRmsg_bol with (n1:= n1)(n2:= m1)(n3:=(n1+m1+1))(b1:= (EQ_M (Mvar (n1+m1+1)) (Mvar n1))) (b2:= FAlse).
simpl in H2.
assert(H4: n1<> n1+m1+1).
omega.
assert (H3: beq_nat n1 (n1+m1+1) = false).
SearchAbout beq_nat.
apply beq_nat_false_iff  with (x:=n1)(y:=n1+m1+1) in H4.
assumption.
rewrite H3 in H2.
simpl. 
rewrite <- beq_nat_refl in H2.
rewrite H2 in H.
assert(H5 :  (Bvar 1) ##  (if_then_else_B (Bvar 1) TRue FAlse)).
rewrite IFTF with (n:=1). reflexivity.
apply Forall_ELM_EVAL_B2 with (n:=1)(b:= (EQ_M (Mvar m1) (Mvar n1))) in H5 .
simpl in H5.
rewrite H5 in H.
assert(H6:(if_then_else_B (Bvar 1) (if_then_else_B (Bvar 2 ) TRue FAlse) FAlse) ## (if_then_else_B (Bvar 2)(if_then_else_B (Bvar 1) TRue FAlse)(if_then_else_B (Bvar 1) FAlse FAlse))).
rewrite <- IFMORPH_B1 with (n2 :=1)(b:=TRue ) (b1:=FAlse)(b2:= FAlse).
reflexivity.
apply Forall_ELM_EVAL_B with (n:=1)(b:= (EQ_M (Mvar n1) (Mvar m1))) in H6 .
simpl in H6.
apply Forall_ELM_EVAL_B with (n:=2)(b:= (EQ_M (Mvar m1) (Mvar n1))) in H6 .
simpl in H6.
pose proof(IFSAME_B).
rewrite IFSAME_B in H6.
rewrite H6 in H.
assert(H7 : (Bvar 1) ## (if_then_else_B (Bvar 1) TRue FAlse)).
rewrite IFTF with (n:=1). reflexivity.
apply Forall_ELM_EVAL_B2 with (n:=1)(b:= (EQ_M (Mvar n1) (Mvar m1))) in H7 .
simpl in H7.
rewrite <- H7 in H.
assert(H8:  (if_then_else_B (EQ_M (Mvar m1) (Mvar n1)) [[ (n1+m1+1):= (Mvar m1)]](EQ_M (Mvar (n1+m1 +1)) (Mvar m1))
      FAlse) ##  (if_then_else_B (EQ_M (Mvar m1) (Mvar n1)) [[ (n1+m1+1):= (Mvar n1)]](EQ_M (Mvar (n1+m1+1)) (Mvar m1))
      FAlse)).
apply EQ_BRmsg_bol with (n1:= m1)(n2:= n1)(n3:=(n1+m1+1))(b1:= (EQ_M (Mvar (n1+m1+1)) (Mvar m1))) (b2:= FAlse).
simpl in H8.
assert(H9: m1<> n1+m1+1).
omega.
assert (H10: beq_nat m1 (n1+m1+1) = false).
apply beq_nat_false_iff  with (x:=m1)(y:=n1+m1+1) in H9.
assumption.
rewrite H10 in H8.
simpl in H8.
rewrite <- beq_nat_refl in H8.
rewrite <- H8 in H.
assert(H11:( EQ_M (Mvar m1) (Mvar m1)) ## TRue).
apply  EQmsg with (x:= (Mvar m1)) (y:= (Mvar m1)).
reflexivity.
rewrite H11 in H.
assert(H12 : (Bvar 1) ## (if_then_else_B (Bvar 1) TRue FAlse)).
rewrite IFTF with (n:=1).
reflexivity.
apply Forall_ELM_EVAL_B2 with (n:=1)(b := (EQ_M (Mvar m1)(Mvar n1))) in H12.
simpl in H12.
rewrite <- H12 in H.
apply H.
Qed.

