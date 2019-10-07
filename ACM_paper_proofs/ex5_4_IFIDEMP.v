(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                     Rohit Chadha <chadhar@missouri.edu>              *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)
Load "ex5_4_IFTF".

(** This library defines a theorem [IFIDEMP] and its proof. Notice that we use [#] (resp. [##]) for [message] (resp. [Bool]) in lieu of [=].

 [if b then (if b then x1 else y1) else (if b then x2 else y2) # if b then x1 else y2] *)

Theorem IFIDEMP_B : forall (n: nat)(b1 b2 b3 b4 : Bool), (if_then_else_B (Bvar n) (if_then_else_B (Bvar n) b1 b2) (if_then_else_B (Bvar n) b3 b4)) ## (if_then_else_B (Bvar n) b1 b4).
Proof.
intros n b1 b2 b3 b4.
rewrite IFEVAL_B with (b1:= if_then_else_B (Bvar n) b1 b2)(b2 := (if_then_else_B (Bvar n) b3 b4)) .
simpl.
rewrite <-beq_nat_refl.
rewrite IFTRUE_B.
rewrite IFFALSE_B.
rewrite IFEVAL_B with(b2:=b4).
reflexivity.               
Qed.

Theorem IFIDEMP_M : forall (n: nat)(x1 x2 y1 y2 : message),  (if_then_else_M (Bvar n) (if_then_else_M (Bvar n) x1 y1) (if_then_else_M (Bvar n) x2 y2)) # (if_then_else_M (Bvar n) x1 y2).
Proof.
intros n x1 x2 y1 y2 .
rewrite IFEVAL_M with (t1:= if_then_else_M (Bvar n) x1 y1)(t2 := (if_then_else_M (Bvar n) x2 y2)) .
simpl.
rewrite <-beq_nat_refl.
rewrite IFTRUE_M.
rewrite IFFALSE_M. 
rewrite IFEVAL_M with (t2:=y2).
reflexivity.
Qed.
