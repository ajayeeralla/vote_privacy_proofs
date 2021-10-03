(************************************************************************)
(* Copyright (c) 2015-2019, Ajay Kumar Eeralla                          *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(************************************************************************)    

Require Export ex11.
(** This library defines a theorem which states that,

[if b then x1 else y1 = if b then x2 else y2 -> if b then t[[x1]] else t'[[y1]] = if b then t[[x2]] else t'[[y2]] ] *)

Theorem Ex12bol_bol: forall (n1 n2 n3 n4 n5 n6 : nat)(b b1 b2:Bool), (IF b then (Bvar n1) else (Bvar n2)) ## (IF b then (Bvar n3) else (Bvar n4)) ->  (IF b then [n5:= (Bvar n1)]b1 else [n6:= (Bvar n2)]b2)  ##  (IF b then [n5:= (Bvar n3)]b1 else [n6:= (Bvar n4)] b2).
Proof.
intros. 
assert (H1:   (IF b then [n5:= IF b then (Bvar n1) else (Bvar n2)] b1 else [n6 := IF b then (Bvar n1) else (Bvar n2)] b2) ## (IF b then [n5:= (Bvar n1)]b1 else [n6:= (Bvar n2)]b2)).
apply Ex9bol_bol1 with  (b1:=b1)(b2:=b2).
rewrite <- H1.
rewrite H.
apply Ex9bol_bol1 with (b1:= b1)(b2:=b2).
Qed.

Theorem Ex12bol_msg: forall (n1 n2 n3 n4 n5 n6 : nat)(b :Bool) (m1 m2 : message), (IF b then (Bvar n1) else (Bvar n2)) ## (IF b then (Bvar n3) else (Bvar n4)) ->  (If b then ((n5:= (Bvar n1))m1) else ((n6:= (Bvar n2)) m2))  #  (If b then ((n5:= (Bvar n3))m1) else ((n6:= (Bvar n4)) m2)).
Proof.
intros. 
pose proof Ex9bol_msg1.
assert (H1:   (If b then ((n5:= IF b then (Bvar n1) else (Bvar n2)) m1) else ((n6 := IF b then (Bvar n1) else (Bvar n2)) m2)) # (If b then ((n5:= (Bvar n1))m1) else ((n6:= (Bvar n2))m2))).
apply Ex9bol_msg1 with  (m1:=m1)(m2:=m2).
rewrite <- H1.
rewrite H.
apply Ex9bol_msg1.
Qed.

Theorem Ex12msg_msg: forall (n1 n2 n3 n4 n5 n6 : nat)(b:Bool)(m1 m2: message),  (If b then (Mvar n1) else (Mvar n2)) # (If b then (Mvar n3) else (Mvar n4)) ->  ( If b then (submsg_msg n5 (Mvar n1) m1) else (submsg_msg n6 (Mvar n2) m2))  # (If b then (submsg_msg n5 (Mvar n3) m1) else  (submsg_msg n6 (Mvar n4) m2)).
Proof.
intros. 
assert (H1:  (If b then (submsg_msg n5  (If b then (Mvar n1) else (Mvar n2)) m1) else (submsg_msg n6 (If b then (Mvar n1) else (Mvar n2)) m2)) # ( If b then (submsg_msg n5  (Mvar n1)  m1) else (submsg_msg n6 (Mvar n2) m2))).
apply Ex9msg_msg1 .
rewrite <-H1.
rewrite H. 
apply Ex9msg_msg1.
Qed.

Theorem Ex12msg_bol: forall (n1 n2 n3 n4 n5 n6 : nat)(b:Bool)(b1 b2: Bool),  (If b then (Mvar n1) else (Mvar n2)) # (If b then (Mvar n3) else (Mvar n4)) ->  ( IF b then ([[ n5 := (Mvar n1)]] b1) else ( [[ n6 := (Mvar n2)]] b2)) ## (IF b then ([[ n5 := (Mvar n3)]] b1) else ([[ n6 := (Mvar n4)]] b2)).
Proof.
intros.
assert (H1:  (IF b then ([[ n5 := (If b then (Mvar n1) else (Mvar n2) )]] b1) else ([[ n6 := (If b then (Mvar n1) else (Mvar n2))]] b2)) ## ( IF b then ( [[ n5 :=  (Mvar n1)]]  b1) else ( [[ n6 :=  (Mvar n2)]] b2))).
apply Ex9msg_bol1 .
rewrite <-H1.
rewrite H. 
apply Ex9msg_bol1.
Qed.
