(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                     Rohit Chadha <chadhar@missouri.edu>              *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)
Load "ex5_4_IFIDEMP".

(** This library defines several theorems of [IFMORPH] and the proofs. Notice that we use [#] (resp. [##]) for [message] (resp. [Bool]) in lieu of [=].
 
[(if b then (if b' then x else y) else z) = (if b' then (if b then x else z) else (if b then y else z))]. *)

Theorem IFMORPH_M1: forall ( x y z : message) (n1 n2:nat),
(if_then_else_M (Bvar n2)(if_then_else_M (Bvar n1)  x y) z) # (if_then_else_M (Bvar n1) (if_then_else_M (Bvar n2)  x  z) (if_then_else_M  (Bvar n2) y z) ).
Proof.
intros.
rewrite <- IFSAME_M with (b:= (Bvar n1)) (x:= (if_then_else_M (Bvar n2) (if_then_else_M (Bvar n1) x y) z)).
rewrite IFEVAL_M.
simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_M.
rewrite IFFALSE_M.
rewrite IFEVAL_M with (t1:= (if_then_else_M (Bvar n2) x z))(t2:= (if_then_else_M (Bvar n2) y z)).
simpl.
reflexivity.
Qed.

Theorem IFMORPH_B1: forall ( b b1 b2 : Bool) (n1 n2:nat) ,
 (if_then_else_B (Bvar n2)(if_then_else_B (Bvar n1)  b b1) b2)  ## (if_then_else_B (Bvar n1) (if_then_else_B (Bvar n2)  b  b2) (if_then_else_B  (Bvar n2) b1 b2) ).
Proof.
intros.
rewrite <- IFSAME_B with (b:= (Bvar n1)) (b1:= (if_then_else_B (Bvar n2) (if_then_else_B (Bvar n1) b b1) b2)).
rewrite IFEVAL_B.
simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_B.
rewrite IFFALSE_B.
rewrite IFEVAL_B with (n:=n1)(b1:= (if_then_else_B (Bvar n2) b b2))(b2:= (if_then_else_B (Bvar n2) b1 b2)).
simpl.
reflexivity.
Qed.
(**For a function [f:Bool -> Bool-> Bool], we have [f(if b then x else y, z , z1) = if b then f(x,z,z1) else f(x,y,z1)] *)

Theorem IFMORPH_B2: forall (n:nat)(b1 b2 b3 b4 : Bool) , 
(if_then_else_B (if_then_else_B (Bvar n) b1 b2 ) b3 b4)  ##  (if_then_else_B (Bvar n) (if_then_else_B  b1  b3 b4 ) (if_then_else_B  b2 b3 b4) ).
Proof.
intros.
pose proof (IFSAME_B).
rewrite <- IFSAME_B with (b:= (Bvar n)) (b1:=(if_then_else_B (if_then_else_B (Bvar n) b1 b2 ) b3 b4)).
pose proof(IFEVAL_B).
rewrite IFEVAL_B.
simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_B.
rewrite IFFALSE_B.
rewrite IFEVAL_B with (b1 := (if_then_else_B b1 b3 b4))(b2:= (if_then_else_B b2 b3 b4)).
simpl.
reflexivity.
Qed.
(**For a function [f: message -> message -> Bool], we have [f(if b then x else y, z , z1) = if b then f(x,z,z1) else f(x,y,z1)] *)
Theorem IFMORPH_M2: forall (n:nat)(b1 b2 :Bool)(y z : message), 
 (if_then_else_M (if_then_else_B (Bvar n) b1 b2 ) y z)  #(if_then_else_M (Bvar n) (if_then_else_M  b1  y z ) (if_then_else_M  b2 y z) ).
Proof.
intros.
rewrite <- IFSAME_M with (b:=(Bvar n))(x:= if_then_else_M (if_then_else_B (Bvar n) b1 b2) y z).
rewrite IFEVAL_M.
simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_B.
rewrite IFFALSE_B.
rewrite IFEVAL_M with (t1:=  (if_then_else_M b1 y z))(t2:= (if_then_else_M b2 y z)).
simpl.
reflexivity.
Qed.

(** For a function [f: Bool -> Bool -> Bool], we have [f(if b then x else y, z) = if b then f(x,z) else f(y,z) ] *)

Theorem IFMORPH_B3: forall  (n n1 n2 n3 :nat), ( EQ_B (if_then_else_B (Bvar n) (Bvar n1) (Bvar n2)) (Bvar n3)) ##  (if_then_else_B (Bvar n) (EQ_B (Bvar n1) (Bvar n3) ) (EQ_B (Bvar n2) (Bvar n3))).
Proof.
intros.
rewrite <- IFSAME_B with (b:=(Bvar n))( b1:= EQ_B (if_then_else_B (Bvar n) (Bvar n1) (Bvar n2)) (Bvar n3)).
rewrite IFEVAL_B.
simpl. rewrite <- beq_nat_refl.
rewrite IFTRUE_B.
rewrite IFFALSE_B.
rewrite IFEVAL_B with (b1:= (EQ_B (Bvar n1) (Bvar n3)))(b2:= (EQ_B (Bvar n2) (Bvar n3))).
simpl.
reflexivity.
Qed.

Theorem IFMORPH_M3: forall  (n n1 n2 n3 :nat), ( EQ_M (if_then_else_M (Bvar n) (Mvar n1) (Mvar n3))  (if_then_else_M (Bvar n) (Mvar n2) (Mvar n3))) ## ( if_then_else_B (Bvar n) (EQ_M (Mvar n1)  (if_then_else_M (Bvar n) (Mvar n2) (Mvar n3) )) (EQ_M (Mvar n3)  (if_then_else_M (Bvar n) (Mvar n2) (Mvar n3)))). 
Proof.
intros.
rewrite <- IFSAME_B with (b:=(Bvar n))( b1:= EQ_M (if_then_else_M (Bvar n) (Mvar n1) (Mvar n3))  (if_then_else_M (Bvar n) (Mvar n2) (Mvar n3))).
rewrite IFEVAL_B.
simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_M.
rewrite IFFALSE_M .
rewrite IFTRUE_M.
rewrite IFFALSE_M.
rewrite IFEVAL_B with (b1:= (EQ_M (Mvar n1) (if_then_else_M (Bvar n) (Mvar n2) (Mvar n3))))(b2:= (EQ_M (Mvar n3) (if_then_else_M (Bvar n) (Mvar n2) (Mvar n3)))).
simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_M.
rewrite IFFALSE_M.
reflexivity.
Qed.

Theorem IFMORPH_M5 : forall (n1 n2 n3 :nat) (m1 m2 m3 m4: message),  (if_then_else_M (Bvar n1) (if_then_else_M (Bvar n2) m1 m2 ) (if_then_else_M (Bvar n3) m3 m4)) # (if_then_else_M (Bvar n2) (if_then_else_M (Bvar n1) m1 (if_then_else_M (Bvar n3) m3 m4)) (if_then_else_M (Bvar n1) m2 (if_then_else_M (Bvar n3) m3 m4))).
Proof. intros. 
pose proof(IFSAME_M (Bvar n2) (if_then_else_M (Bvar n1) (if_then_else_M (Bvar n2) m1 m2 ) (if_then_else_M (Bvar n3) m3 m4))).
rewrite IFEVAL_M with (n:= n2) (t1:= (if_then_else_M (Bvar n1) (if_then_else_M (Bvar n2) m1 m2 ) (if_then_else_M (Bvar n3) m3 m4))) (t2 := (if_then_else_M (Bvar n1) (if_then_else_M (Bvar n2) m1 m2 ) (if_then_else_M (Bvar n3) m3 m4))) in H.
simpl in H.
repeat rewrite <- beq_nat_refl in H.
rewrite <-H. 
rewrite IFEVAL_M with (n:= n2) (t1:= (if_then_else_M (Bvar n1) m1 (if_then_else_M (Bvar n3) m3 m4))) (t2 := (if_then_else_M (Bvar n1) m2 (if_then_else_M (Bvar n3) m3 m4))).
simpl. rewrite  IFTRUE_M, IFFALSE_M.
reflexivity. Qed.

Theorem IFMORPH_M6 : forall(n1 n2 :nat) (m1 m2 m3:message), (if_then_else_M (Bvar n1) m1 (if_then_else_M (Bvar n2) m2 m3)) # (if_then_else_M (Bvar n2) (if_then_else_M (Bvar n1) m1 m2) (if_then_else_M (Bvar n1)  m1 m3)).
Proof. intros. pose proof(IFSAME_M (Bvar n2)  (if_then_else_M (Bvar n1) m1 (if_then_else_M (Bvar n2) m2 m3))).
rewrite IFEVAL_M in H.
simpl in H. repeat rewrite <- beq_nat_refl in H.
rewrite  IFTRUE_M, IFFALSE_M in H.
rewrite <-H. clear H.
rewrite IFEVAL_M with (t1:= (if_then_else_M (Bvar n1) m1 m2)).
simpl. reflexivity. Qed.
(*
Axiom IFMORPH_B4: forall  (n1:nat) (b1 b2 b3:Bool), (if_then_else_B (Bvar n1) b1 (if_then_else_B (Bvar (n1+1)) b2 b3))  ## (if_then_else_B (Bvar (n1+1)) (if_then_else_B (Bvar n1) b1 b2) (if_then_else_B (Bvar n1) b1 b3)) .
*)

Theorem IFMORPH_M4 : forall (n1:nat) (m1 m2 m3 : message), (if_then_else_M (Bvar n1) m1 (if_then_else_M (Bvar (n1+1)) m2 m3) ) # (if_then_else_M (Bvar (n1+1)) (if_then_else_M (Bvar n1) m1 m2)(if_then_else_M (Bvar n1) m1 m3)).
Proof. 
intros.
rewrite <- IFSAME_M with (b:= (Bvar (n1+1))) (x:= (if_then_else_M (Bvar n1)  m1 (if_then_else_M (Bvar (n1+1)) m2 m3))).
rewrite IFEVAL_M.
simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_M.
rewrite IFFALSE_M.
assert(H: beq_nat n1 (n1 +1) = false).
induction n1.
simpl.  reflexivity.
simpl. 
rewrite IHn1. 
reflexivity. 
rewrite H.
 rewrite IFEVAL_M with (t1:=(if_then_else_M (Bvar n1) m1 m2) )(t2:= (if_then_else_M (Bvar n1) m1 m3) ).
simpl.
rewrite H.
reflexivity.
Qed.
