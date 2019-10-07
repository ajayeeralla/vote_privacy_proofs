(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                     Rohit Chadha <chadhar@missouri.edu>              *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)

Load "ex7_3".
(** This library defines a theorem which states that,

[if b then x1 else y1 = if b then x2 else y2 -> if b then t[[x1]] else t'[[y1]] = if b then t[[x2]] else t'[[y2]] ] *)

Theorem Ex12bol_bol: forall (n1 n2 n3 n4 n5 n6 : nat)(b b1 b2:Bool),   (if_then_else_B b (Bvar n1) (Bvar n2)) ## (if_then_else_B b (Bvar n3) (Bvar n4)) ->  (if_then_else_B b [n5:= (Bvar n1)]b1 [n6:= (Bvar n2)]b2)  ##  (if_then_else_B b [n5:= (Bvar n3)]b1  [n6:= (Bvar n4)] b2).
Proof.
intros. 
assert (H1:   (if_then_else_B b [n5:= if_then_else_B b (Bvar n1) (Bvar n2)] b1 [n6 := if_then_else_B b (Bvar n1) (Bvar n2)] b2) ## (if_then_else_B b [n5:= (Bvar n1)]b1 [n6:= (Bvar n2)]b2)).
apply Ex9bol_bol1 with  (b1:=b1)(b2:=b2).
rewrite <- H1.
rewrite H.
apply Ex9bol_bol1 with (b1:= b1)(b2:=b2).
Qed.

Theorem Ex12bol_msg: forall (n1 n2 n3 n4 n5 n6 : nat)(b :Bool) (m1 m2 : message),   (if_then_else_B b (Bvar n1) (Bvar n2)) ## (if_then_else_B b (Bvar n3) (Bvar n4)) ->  (if_then_else_M b ((n5:= (Bvar n1))m1) ((n6:= (Bvar n2)) m2))  #  (if_then_else_M b ((n5:= (Bvar n3))m1)  ((n6:= (Bvar n4)) m2)).
Proof.
intros. 
pose proof Ex9bol_msg1.
assert (H1:   (if_then_else_M b ((n5:= if_then_else_B b (Bvar n1) (Bvar n2)) m1) ((n6 := if_then_else_B b (Bvar n1) (Bvar n2)) m2)) # (if_then_else_M b ((n5:= (Bvar n1))m1) ((n6:= (Bvar n2))m2))).
apply Ex9bol_msg1 with  (m1:=m1)(m2:=m2).
rewrite <- H1.
rewrite H.
apply Ex9bol_msg1.
Qed.

Theorem Ex12msg_msg: forall (n1 n2 n3 n4 n5 n6 : nat)(b:Bool)(m1 m2: message),  (if_then_else_M b (Mvar n1) (Mvar n2)) # (if_then_else_M b (Mvar n3) (Mvar n4)) ->  ( if_then_else_M b (submsg_msg n5 (Mvar n1) m1)  (submsg_msg n6 (Mvar n2) m2))  # (if_then_else_M b (submsg_msg n5 (Mvar n3) m1)  (submsg_msg n6 (Mvar n4) m2)).
Proof.
intros. 
assert (H1:  (if_then_else_M b (submsg_msg n5  (if_then_else_M b (Mvar n1) (Mvar n2)) m1) (submsg_msg n6 (if_then_else_M b (Mvar n1) (Mvar n2)) m2)) # ( if_then_else_M b (submsg_msg n5  (Mvar n1)  m1) (submsg_msg n6 (Mvar n2) m2))).
apply Ex9msg_msg1 .
rewrite <-H1.
rewrite H. 
apply Ex9msg_msg1.
Qed.

Theorem Ex12msg_bol: forall (n1 n2 n3 n4 n5 n6 : nat)(b:Bool)(b1 b2: Bool),  (if_then_else_M b (Mvar n1) (Mvar n2)) # (if_then_else_M b (Mvar n3) (Mvar n4)) ->  ( if_then_else_B b  ([[ n5 := (Mvar n1)]] b1)  ( [[ n6 := (Mvar n2)]] b2)) ## (if_then_else_B b ([[ n5 := (Mvar n3)]] b1)  ([[ n6 := (Mvar n4)]] b2)).
Proof.
intros. 
assert (H1:  (if_then_else_B b ( [[ n5 := (if_then_else_M b (Mvar n1) (Mvar n2) )]] b1) ([[ n6 := (if_then_else_M b (Mvar n1) (Mvar n2))]] b2)) ## ( if_then_else_B b ( [[ n5 :=  (Mvar n1)]]  b1) ( [[ n6 :=  (Mvar n2)]] b2))).
apply Ex9msg_bol1 .
rewrite <-H1.
rewrite H. 
apply Ex9msg_bol1.
Qed.
