(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                     Rohit Chadha <chadhar@missouri.edu>              *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)
Load "cor_ex7_2".

(** This library defines a theorem that states, 

[if EQ(x1 , x2) then x1 else y = if EQ(x1 ,x2) then x2 else y] *)

Theorem Example11_M:   (if_then_else_M (EQ_M  (Mvar 1) (Mvar 2)) (Mvar 1) (Mvar 3)) # (if_then_else_M (EQ_M  (Mvar 1) (Mvar 2)) (Mvar 2) (Mvar 3)) .
Proof.
intros.
rewrite EQmsg .
(assert(H1:  (EQ_M (if_then_else_M (Bvar 0) (Mvar 1) (Mvar 3) ) (if_then_else_M (Bvar 0) (Mvar 2) (Mvar 3) )) ## (if_then_else_B (Bvar 0) (EQ_M  (Mvar 1) (if_then_else_M (Bvar 0) (Mvar 2) (Mvar 3) ))  (EQ_M  (Mvar 3) (if_then_else_M (Bvar 0) (Mvar 2) (Mvar 3) ))))).
apply IFMORPH_M3 with (n:=0) (n1:=1)(n2:=2)(n3:=3)  .
apply Forall_ELM_EVAL_B  with (n:=0) (b:= (EQ_M (Mvar 1) (Mvar 2))) in H1.
simpl in H1.
assert (H2: (if_then_else_B (Bvar 0)
    [[4 := if_then_else_M (Bvar 0) (Mvar 2) (Mvar 3)]](EQ_M (Mvar 1) (Mvar 4))
    [[4 := if_then_else_M (Bvar 0) (Mvar 2) (Mvar 3)]](EQ_M (Mvar 3) (Mvar 4))) ##
  ( if_then_else_B (Bvar 0) [[4 := Mvar 2]](EQ_M (Mvar 1) (Mvar 4))
    [[4 := Mvar 3]](EQ_M (Mvar 3) (Mvar 4))) ).
apply Ex9msg_bol1 with (b:= (Bvar 0))(n1:=2)(n2:=3)(n3:=2)(n4:=3)(n5:=4)(n6:= 4) (b1:= (EQ_M (Mvar 1) (Mvar 4))) (b2:= (EQ_M (Mvar 3) (Mvar 4))) .
simpl in H2.
apply Forall_ELM_EVAL_B  with (n:=0) (b:= (EQ_M (Mvar 1) (Mvar 2))) in H2.
simpl in H2.
rewrite H2 in H1 .
rewrite H1.
assert (H3:   (EQ_M (Mvar 3) (Mvar 3)) ##   TRue).
apply EQmsg with (x:=(Mvar 3))( y:= (Mvar 3)).
reflexivity. 
rewrite H3.
assert (H4: (if_then_else_B (Bvar 0) TRue FAlse) ## (Bvar 0)).
apply IFTF with (n:=0).
apply Forall_ELM_EVAL_B2 with (n :=0)(b:= (EQ_M (Mvar 1) (Mvar 2))) in H4.
simpl  in H4.
assert(H6:  (if_then_else_B (Bvar 0) (Bvar 0) TRue) ## (if_then_else_B (Bvar 0) TRue TRue)).
apply IFEVAL_B with (n:=0) (b1:=(Bvar 0)) (b2:= TRue) .
apply Forall_ELM_EVAL_B with (n :=0)(b:= (EQ_M (Mvar 1) (Mvar 2))) in H6.
simpl  in H6.
rewrite H6.
apply IFSAME_B.
Qed.

Theorem Example11_B:    (if_then_else_B (EQ_B  (Bvar 1) (Bvar 2)) (Bvar 1) (Bvar 3)) ## ( if_then_else_B (EQ_B  (Bvar 1) (Bvar 2)) (Bvar 2) (Bvar 3) ).
Proof.
intros.
rewrite EQ_Bool .
(assert(H1:  (EQ_B (if_then_else_B (Bvar 0) (Bvar 1) (Bvar 3) ) (if_then_else_B (Bvar 0) (Bvar 2) (Bvar 3) )) ## (if_then_else_B (Bvar 0) (EQ_B  (Bvar 1) (if_then_else_B (Bvar 0) (Bvar 2) (Bvar 3) ))  (EQ_B  (Bvar 3) (if_then_else_B (Bvar 0) (Bvar 2) (Bvar 3) ))))).
assert (H2 : (EQ_B (if_then_else_B (Bvar 0) (Bvar 1) (Bvar  3)) (Bvar 4)) ## ( if_then_else_B (Bvar 0) (EQ_B (Bvar 1) (Bvar 4) ) (EQ_B (Bvar 3) (Bvar 4)))).
apply IFMORPH_B3 with  (n:=0) (n1:=1).
apply Forall_ELM_EVAL_B  with (n:=4) (b:= if_then_else_B (Bvar 0) (Bvar 2) (Bvar 3) )in H2.
simpl in H2.
apply H2.
apply Forall_ELM_EVAL_B  with (n:=0) (b:= (EQ_B (Bvar 1) (Bvar 2))) in H1.
simpl in H1.
assert (H2:  (if_then_else_B (Bvar 0) (EQ_B (Bvar 1) (if_then_else_B (Bvar 0) (Bvar 2) (Bvar 3) ) )   (EQ_B (Bvar 3) (if_then_else_B (Bvar 0) (Bvar 2) (Bvar 3) ) )) ## (if_then_else_B (Bvar 0) (EQ_B (Bvar 1) (Bvar 2) ) ( EQ_B (Bvar 3) (Bvar 3))  )).
apply Ex9bol_bol1 with (n1:=2)(n2:=3)(n3:=2)(n4:=3)(n5:=4)(n6:= 4) (b1:= (EQ_B (Bvar 1) (Bvar 4))) (b2:= (EQ_B (Bvar 3) (Bvar 4))) .
apply Forall_ELM_EVAL_B  with (n:=0) (b:= (EQ_B (Bvar 1) (Bvar 2))) in H2.
simpl in H2.
rewrite H1 .
rewrite H2.
assert (H3:   (EQ_B (Bvar 3) (Bvar 3)) ## TRue).
apply EQ_Bool with (x:=(Bvar 3))( y:= (Bvar 3)).
reflexivity.
rewrite H3. 
assert (H4: (if_then_else_B (Bvar 0) TRue FAlse) ## (Bvar 0)).
apply IFTF with (n:=0).
apply Forall_ELM_EVAL_B2 with (n :=0)(b:= (EQ_B (Bvar 1) (Bvar 2))) in H4.
simpl  in H4.
assert(H6: (if_then_else_B (Bvar 0) (Bvar 0) TRue) ## ( if_then_else_B (Bvar 0) TRue TRue)).
apply IFEVAL_B with (n:=0) (b1:=(Bvar 0)) (b2:= TRue) .
apply Forall_ELM_EVAL_B with (n :=0)(b:= (EQ_B (Bvar 1) (Bvar 2))) in H6.
simpl  in H6.
rewrite H6.
apply IFSAME_B.
Qed.

Axiom Example11_B1: forall (n1 n2 n3 :nat), (if_then_else_B (EQ_B  (Bvar n1) (Bvar n2)) (Bvar n1) (Bvar n3))  ## ( if_then_else_B (EQ_B  (Bvar n1) (Bvar n2)) (Bvar n2) (Bvar n3)).
Axiom Example11_B2: forall (n1 n2 n3 :nat),  (if_then_else_B (EQ_M  (Mvar n1) (Mvar n2)) (Bvar n1) (Bvar n3))  ## (if_then_else_B (EQ_M  (Mvar n1) (Mvar n2)) (Bvar n2) (Bvar n3)).
Axiom Example11_M1:forall(n1 n2 n3:nat),   (if_then_else_M (EQ_M  (Mvar n1) (Mvar n2)) (Mvar n1) (Mvar n3) ) # (if_then_else_M (EQ_M  (Mvar n1) (Mvar n2)) (Mvar n2) (Mvar n3)).
Axiom Example11_M2:forall(n1 n2 n3:nat),   (if_then_else_M (EQ_B  (Bvar n1) (Bvar n2)) (Mvar n1) (Mvar n3) ) # (if_then_else_M (EQ_B  (Bvar n1) (Bvar n2)) (Mvar n2) (Mvar n3)).
