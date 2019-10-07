(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                     Rohit Chadha <chadhar@missouri.edu>              *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)
Load "andbprops".

(** This library defines a theorem and its proof. Notice that we use [#] (resp. [##]) for [message] (resp. [Bool]) in lieu of [=] .

[ if b then t1[[if b then x1 else y1]] else t2[[if b then x2 else y2]] = if b then t1[[x1]] else t2[[y2]] ] *)

(*Bool in Bool*)
(** tactic Fr_pf1 *)
Ltac Fr_pf1 := 
repeat match goal with 
| [ |- beq_nat ?X ?Y = ?Z] => destruct (beq_nat X Y) ;  match goal with | [H1: context [ if beq_nat ?X' ?Y' then ?Z' else ?Z''] |- _ ] =>  simpl in H1; repeat rewrite <- beq_nat_refl in H1 ; simpl in H1;  symmetry  end end; try assumption ; try reflexivity;
   repeat match goal with 
| [ H : beq_nat ?X ?Y = _ |- _ ] =>  match goal with | [H1: context [ if beq_nat ?X ?Y then _ else _ ] |- _ ] =>  rewrite H in H1;  simpl in H1 end end; try assumption ; try reflexivity.

Theorem Ex9bol_bol: forall (b1 b2: Bool )(n n1 n2 n3 n4 n5 n6 :nat),  (notoccur_nlist n [n1 ; n2 ; n3;n4] = true)  /\ (notoccur_blist n [b1 ; b2]  = true) 
                     ->  (if_then_else_B (Bvar n) ([n5:= (if_then_else_B (Bvar n) (Bvar n1) (Bvar n2))] b1) ([n6:=  (if_then_else_B (Bvar n) (Bvar n3) (Bvar n4))] b2))
                      ##  ( if_then_else_B (Bvar n) ([n5:= (Bvar n1)] b1)                                     ([n6:= (Bvar n4)] b2) ) .
Proof.
intros.
inversion H.
(************notoccn_nlist n [n1; n2; n3; n4] = true -> n<> n1/\ n<> n2/\ n<> n3/\ n<> n4 ********************)
unfold notoccur_nlist in H0.
assert(H2: beq_nat n1 n  = false).
destruct(beq_nat n1 n).
-inversion H0.
-reflexivity.
-assert(H3: beq_nat n2 n  = false).
+destruct(beq_nat n2 n).
{inversion H0. rewrite H2. reflexivity. }
{reflexivity. }
+assert(H4: beq_nat n3 n  = false).
destruct(beq_nat n3 n).
inversion H0.
rewrite H2.
rewrite H3.
reflexivity.
reflexivity.
assert(H5 : beq_nat n4 n  = false).
destruct(beq_nat n4 n).
inversion H0.
rewrite H2.
rewrite H3.
rewrite H4.
reflexivity.
reflexivity.
rewrite IFEVAL_B with(n:=n)(b1:=  [n5 := if_then_else_B (Bvar n) (Bvar n1) (Bvar n2)](b1)) (b2:=  [n6 := if_then_else_B (Bvar n) (Bvar n3) (Bvar n4)](b2)).
rewrite  notocc_bolbb with (n1 :=n ) (n2:=n5) (b := TRue) (b1:= if_then_else_B (Bvar n) (Bvar n1) (Bvar n2))(b2:= b1).
 simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_B .
try rewrite H2; try rewrite H3; try rewrite H4; try rewrite H5.
simpl.
rewrite  notocc_bolbb with (n1 :=n ) (n2:=n6) (b := FAlse) (b1:= if_then_else_B (Bvar n) (Bvar n3) (Bvar n4))(b2:= b2).
simpl.
rewrite <- beq_nat_refl.
try rewrite H2; try rewrite H3; try rewrite H4; try rewrite H5.
rewrite IFFALSE_B. reflexivity.
inversion H1; apply andb_prop in H7;inversion H7;rewrite H8; rewrite H6; apply andb_prop in H8; inversion H8;
try rewrite H9; reflexivity.
inversion H1;apply andb_prop in H7;inversion H7;rewrite H8; rewrite H6; apply andb_prop in H8; inversion H8;
try rewrite H9; reflexivity.
Qed.


Theorem Ex9bol_bol1: forall (b b1 b2: Bool )( n1 n2 n3 n4 n5 n6 :nat),   (if_then_else_B b ([n5:= (if_then_else_B b (Bvar n1) (Bvar n2))] b1) ([n6:=  (if_then_else_B b (Bvar n3) (Bvar n4))] b2))
                      ##  ( if_then_else_B b ([n5:= (Bvar n1)] b1)                                     ([n6:= (Bvar n4)] b2) ) .

Proof.
intros.
assert(H:  exists n:nat, (notoccur_nlist n [n1 ; n2;n3;n4] = true ) /\(notoccur_blist n [ b1 ; b2  ] = true)  ).
pose proof (existsn_Mlist).
apply existsn_Blist with (m1:=4) (nl := [n1 ; n2;n3;n4]) (bl := [ b1 ; b2 ])(m2:=2).
inversion H as [z H1].
inversion H1.
unfold notoccur_nlist in H0.
inversion H2.
assert(H5: beq_nat n1 z = false).
destruct(beq_nat n1 z).
inversion H1.
rewrite <- H0.
reflexivity.
reflexivity.
assert(H6: beq_nat n2 z =false).
destruct(beq_nat n2 z).
rewrite H5 in H0.
simpl in H0.
rewrite <- H0. reflexivity.
reflexivity.
assert(H7: beq_nat n3 z = false).
destruct (beq_nat n3 z).
rewrite H5 in H0.
rewrite H6 in H0. simpl in H0. rewrite <- H0. reflexivity. reflexivity.
assert(H8: beq_nat n4 z = false).
destruct (beq_nat n4 z).
simpl in H0.
rewrite H5 in H0.
rewrite H6 in H0.
rewrite H7 in H0.
rewrite <- H0. try  repeat reflexivity. reflexivity.
apply Ex9bol_bol with (n5:= n5)(n6:=n6)in H1.
apply Forall_ELM_EVAL_B with (n:=z)(b:= b)in H1.
simpl in H1.
(**destruct Boolblbl with (n:=z)(n1:= n5)(b:=b)(b1:= if_then_else_B (Bvar z) (Bvar n1) (Bvar n2))(b2:= b1) in H1.**)
 rewrite  notocc_bolbb with (n1 :=z ) (n2:=n5) (b := b) (b1:= if_then_else_B (Bvar z) (Bvar n1) (Bvar n2))(b2:= b1) in H1.
rewrite <- beq_nat_refl in H1.
simpl in H1.
rewrite <- beq_nat_refl in H1.
try rewrite H5 in H1; try rewrite H6 in H1; try rewrite H7 in H1; try rewrite H8 in H1.
rewrite  notocc_bolbb with (n1 :=z ) (n2:=n6) (b := b) (b1:= if_then_else_B (Bvar z) (Bvar n3) (Bvar n4))(b2:= b2) in H1.
simpl in H1; rewrite <- beq_nat_refl in H1 ;
try rewrite H5 in H1; try rewrite H6 in H1; try rewrite H7 in H1; try rewrite H8 in H1.
rewrite  notocc_bolbb with (n1 :=z ) (n2:=n5) (b := b) (b1:= (Bvar n1))(b2:= b1) in H1. 
rewrite  notocc_bolbb with (n1 :=z ) (n2:=n6) (b := b) (b1:= (Bvar n4))(b2:= b2) in H1.
simpl in H1.
try rewrite H5 in H1; try rewrite H6 in H1; try rewrite H7 in H1; try rewrite H8 in H1.
rewrite H1. reflexivity.
inversion H4; apply andb_prop in H4; inversion H4 ;apply andb_prop in H10 ;inversion H10;
try rewrite H3; try rewrite H11; reflexivity. 
inversion H4; apply andb_prop in H4; inversion H4 ;apply andb_prop in H10 ;inversion H10;
try rewrite H3; try rewrite H11; reflexivity. 
inversion H4; apply andb_prop in H4; inversion H4 ;apply andb_prop in H10 ;inversion H10;
try rewrite H3; try rewrite H11; reflexivity. 
inversion H4; apply andb_prop in H4; inversion H4 ;apply andb_prop in H10 ;inversion H10;
try rewrite H3; try rewrite H11; reflexivity. 
Qed.





Theorem Ex9bol_msg: forall (m1 m2: message )(n n1 n2 n3 n4 n5 n6 :nat),  (notoccur_nlist n [n1 ; n2 ; n3;n4] = true)  /\ (notoccur_mlist n [m1 ; m2]  = true) 
                     -> (if_then_else_M  (Bvar n) ((n5:=  (if_then_else_B (Bvar n) (Bvar n1) (Bvar n2))) m1)
((n6:=  (if_then_else_B (Bvar n) (Bvar n3) (Bvar n4))) m2)) #  (if_then_else_M (Bvar n) ( (n5:= (Bvar n1)) m1) ((n6:= (Bvar n4)) m2) )  .
Proof. 
intros.
inversion H.
(************notoccn_nlist n [n1; n2; n3; n4] = true -> n<> n1/\ n<> n2/\ n<> n3/\ n<> n4 ********************)
unfold notoccur_nlist in H0.
assert(H2: beq_nat n1 n  = false).
destruct(beq_nat n1 n).
inversion H0.
reflexivity.

assert(H3: beq_nat n2 n  = false).
destruct(beq_nat n2 n).
inversion H0.
rewrite H2.

reflexivity.
reflexivity.
assert(H4: beq_nat n3 n  = false).
destruct(beq_nat n3 n).
inversion H0.
rewrite H2.
rewrite H3.

reflexivity.
reflexivity.

assert(H5 : beq_nat n4 n  = false).
destruct(beq_nat n4 n).
inversion H0.
rewrite H2.
rewrite H3.
rewrite H4.
reflexivity.
reflexivity. 
rewrite IFEVAL_M with  (t1:=  (n5 := if_then_else_B (Bvar n) (Bvar n1) (Bvar n2))(m1)) (t2:=  (n6 := if_then_else_B (Bvar n) (Bvar n3) (Bvar n4))(m2)).
rewrite notocc_bolbm with (n1 := n) (b := TRue) (n2:= n5) (b1 := (if_then_else_B (Bvar n) (Bvar n1) (Bvar n2))) (m:= m1).
simpl ;rewrite <- beq_nat_refl.
try rewrite H2; try rewrite H3; try rewrite H4; try rewrite H5.
rewrite IFTRUE_B .
rewrite notocc_bolbm with (n1 := n) (b := FAlse) (n2:= n6) (b1 := (if_then_else_B (Bvar n) (Bvar n3) (Bvar n4))) (m:= m2).
simpl ;rewrite <- beq_nat_refl.
try rewrite H2; try rewrite H3; try rewrite H4; try rewrite H5.
rewrite IFFALSE_B .
reflexivity.
inversion H1; apply andb_prop in H7;inversion H7;rewrite H8; rewrite H6; apply andb_prop in H8; inversion H8;
try rewrite H9; reflexivity.
inversion H1;apply andb_prop in H7;inversion H7;rewrite H8; rewrite H6; apply andb_prop in H8; inversion H8;
try rewrite H9; reflexivity.
Qed.

Theorem Ex9bol_msg1: forall (b : Bool ) (m1 m2 : message)(n1 n2 n3 n4 n5 n6:nat) ,  (if_then_else_M b ((n5:=  (if_then_else_B b (Bvar n1) (Bvar n2))) m1)
((n6:=  (if_then_else_B b (Bvar n3) (Bvar n4))) m2)) #  (if_then_else_M b ( (n5:= (Bvar n1)) m1) ((n6:= (Bvar n4)) m2) ) .
Proof.
intros.
assert(H:  exists n:nat, (notoccur_nlist n [n1 ; n2;n3;n4] = true ) /\(notoccur_mlist n [ m1 ; m2  ] = true)  ).
pose proof (existsn_Mlist).
apply existsn_Mlist with (m1:=4) (nl := [n1 ; n2;n3;n4]) (ml := [ m1 ; m2 ])(m2:=2).
inversion H as [z H1].
inversion H1.
unfold notoccur_nlist in H0.
inversion H2.
assert(H5: beq_nat n1 z = false).
destruct(beq_nat n1 z).
inversion H1.
rewrite <- H0.
reflexivity.
reflexivity.
assert(H6: beq_nat n2 z =false).
destruct(beq_nat n2 z).
rewrite H5 in H0.
simpl in H0.
rewrite <- H0. reflexivity.
reflexivity.
assert(H7: beq_nat n3 z = false).
destruct (beq_nat n3 z).
rewrite H5 in H0.
rewrite H6 in H0. simpl in H0. rewrite <- H0. reflexivity. reflexivity.
assert(H8: beq_nat n4 z = false).
destruct (beq_nat n4 z).

simpl in H0.

rewrite H5 in H0.
rewrite H6 in H0.
rewrite H7 in H0.
rewrite <- H0. try  repeat reflexivity. reflexivity.
apply Ex9bol_msg with (n5:= n5)(n6:=n6)in H1.
apply Forall_ELM_EVAL_M with (n:=z) (x:= b)in H1.
simpl in H1.

(**destruct Boolblbl with (n:=z)(n1:= n5)(b:=b)(b1:= if_then_else_B (Bvar z) (Bvar n1) (Bvar n2))(b2:= b1) in H1.**)
 rewrite  notocc_bolbm with (n1 :=z ) (n2:=n5) (b := b) (b1:= if_then_else_B (Bvar z) (Bvar n1) (Bvar n2))(m:= m1) in H1.
rewrite <- beq_nat_refl in H1.

simpl in H1.
rewrite <- beq_nat_refl in H1.
try rewrite H5 in H1; try rewrite H6 in H1; try rewrite H7 in H1; try rewrite H8 in H1.

rewrite  notocc_bolbm with (n1 :=z ) (n2:=n6) (b := b) (b1:= if_then_else_B (Bvar z) (Bvar n3) (Bvar n4))(m:= m2) in H1.
simpl in H1; rewrite <- beq_nat_refl in H1 ;
try rewrite H5 in H1; try rewrite H6 in H1; try rewrite H7 in H1; try rewrite H8 in H1.
rewrite  notocc_bolbm with (n1 :=z ) (n2:=n5) (b := b) (b1:= (Bvar n1))(m:= m1) in H1. 
rewrite  notocc_bolbm with (n1 :=z ) (n2:=n6) (b := b) (b1:= (Bvar n4))(m:= m2) in H1.
simpl in H1.
try rewrite H5 in H1; try rewrite H6 in H1; try rewrite H7 in H1; try rewrite H8 in H1.
rewrite H1. reflexivity.

inversion H4; apply andb_prop in H4; inversion H4 ;apply andb_prop in H10 ;inversion H10;
try rewrite H3; try rewrite H11; reflexivity. 

inversion H4; apply andb_prop in H4; inversion H4 ;apply andb_prop in H10 ;inversion H10;
try rewrite H3; try rewrite H11; reflexivity. 

inversion H4; apply andb_prop in H4; inversion H4 ;apply andb_prop in H10 ;inversion H10;
try rewrite H3; try rewrite H11; reflexivity. 
inversion H4; apply andb_prop in H4; inversion H4 ;apply andb_prop in H10 ;inversion H10;
try rewrite H3; try rewrite H11; reflexivity. 
Qed.


(****message in message*******************)

Theorem Ex9msg_msg: forall (m1 m2: message )(n n1 n2 n3 n4 n5 n6 :nat),  (notoccur_nlist n [n1 ; n2 ; n3;n4] = true)  /\ (notoccur_mlist n [m1 ; m2]  = true) 
                     ->  (if_then_else_M (Bvar n)(submsg_msg n5  (if_then_else_M (Bvar n) (Mvar n1) (Mvar n2) ) m1)
(submsg_msg n6 (if_then_else_M (Bvar n) (Mvar n3) (Mvar n4) ) m2 ) )  #(if_then_else_M  (Bvar n)  (submsg_msg n5 (Mvar n1) m1) (submsg_msg n6 (Mvar n4) m2)) .
Proof.

Proof. 
intros.
inversion H.
(************notoccn_nlist n [n1; n2; n3; n4] = true -> n<> n1/\ n<> n2/\ n<> n3/\ n<> n4 ********************)
unfold notoccur_nlist in H0.
assert(H2: beq_nat n1 n  = false).
destruct(beq_nat n1 n).
inversion H0.
reflexivity.
assert(H3: beq_nat n2 n  = false).
destruct(beq_nat n2 n).
inversion H0.
rewrite H2.
reflexivity.
reflexivity.
assert(H4: beq_nat n3 n  = false).
destruct(beq_nat n3 n).
inversion H0.
rewrite H2.
rewrite H3.
reflexivity.
reflexivity.
assert(H5 : beq_nat n4 n  = false).
destruct(beq_nat n4 n).
inversion H0.
rewrite H2.
rewrite H3.
rewrite H4.
reflexivity.
reflexivity. 
rewrite IFEVAL_M with  (t1:=  {{n5 := (if_then_else_M (Bvar n) (Mvar n1) (Mvar n2))}}(m1)) (t2:=  {{n6 :=  (if_then_else_M (Bvar n) (Mvar n3) (Mvar n4))}}(m2)).
rewrite notocc_bolmm with (n1 := n) (b := TRue) (n2:= n5) (m1 := if_then_else_M (Bvar n) (Mvar n1) (Mvar n2)) (m2:= m1).
simpl ;rewrite <- beq_nat_refl.
try rewrite H2; try rewrite H3; try rewrite H4; try rewrite H5.
rewrite IFTRUE_M .
rewrite notocc_bolmm with (n1 := n) (b := FAlse) (n2:= n6) (m1 := if_then_else_M (Bvar n) (Mvar n3) (Mvar n4)) (m2:= m2).
simpl ;rewrite <- beq_nat_refl.
try rewrite H2; try rewrite H3; try rewrite H4; try rewrite H5.
rewrite IFFALSE_M .
reflexivity.
inversion H1; apply andb_prop in H7;inversion H7;rewrite H8; rewrite H6; apply andb_prop in H8; inversion H8;
try rewrite H9; reflexivity.
inversion H1;apply andb_prop in H7;inversion H7;rewrite H8; rewrite H6; apply andb_prop in H8; inversion H8;
try rewrite H9; reflexivity.

Qed.

Theorem Ex9msg_msg1: forall (m1 m2: message )(b:Bool)(n1 n2 n3 n4 n5 n6 :nat) , (if_then_else_M b (submsg_msg n5  (if_then_else_M b (Mvar n1) (Mvar n2) ) m1)
(submsg_msg n6 (if_then_else_M b (Mvar n3) (Mvar n4) ) m2 ) ) #  ( if_then_else_M  b  (submsg_msg n5 (Mvar n1) m1) (submsg_msg n6 (Mvar n4) m2) ) .

Proof.


intros.
assert(H:  exists n:nat, (notoccur_nlist n [n1 ; n2;n3;n4] = true ) /\(notoccur_mlist n [ m1 ; m2  ] = true)  ).
pose proof (existsn_Mlist).
apply existsn_Mlist with (m1:=4) (nl := [n1 ; n2;n3;n4]) (ml := [ m1 ; m2 ])(m2:=2).
inversion H as [z H1].
inversion H1.
unfold notoccur_nlist in H0.
inversion H2.
assert(H5: beq_nat n1 z = false).
destruct(beq_nat n1 z).
inversion H1.
rewrite <- H0.
reflexivity.
reflexivity.
assert(H6: beq_nat n2 z =false).
destruct(beq_nat n2 z).
rewrite H5 in H0.
simpl in H0.
rewrite <- H0. reflexivity.
reflexivity.
assert(H7: beq_nat n3 z = false).
destruct (beq_nat n3 z).
rewrite H5 in H0.
rewrite H6 in H0. simpl in H0. rewrite <- H0. reflexivity. reflexivity.
assert(H8: beq_nat n4 z = false).
destruct (beq_nat n4 z).

simpl in H0.

rewrite H5 in H0.
rewrite H6 in H0.
rewrite H7 in H0.
rewrite <- H0. try  repeat reflexivity. reflexivity.
apply Ex9msg_msg with (n5:= n5)(n6:=n6)in H1.
apply Forall_ELM_EVAL_M with (n:=z) (x:= b)in H1.
simpl in H1.

(**destruct Boolblbl with (n:=z)(n1:= n5)(b:=b)(b1:= if_then_else_B (Bvar z) (Bvar n1) (Bvar n2))(b2:= b1) in H1.**)
 rewrite  notocc_bolmm with (n1 :=z ) (n2:=n5) (b := b) (m1 := if_then_else_M (Bvar z) (Mvar n1) (Mvar n2))(m2:= m1) in H1.
rewrite <- beq_nat_refl in H1.

simpl in H1.
rewrite <- beq_nat_refl in H1.
try rewrite H5 in H1; try rewrite H6 in H1; try rewrite H7 in H1; try rewrite H8 in H1.

rewrite  notocc_bolmm with (n1 :=z ) (n2:=n6) (b := b) (m1:= if_then_else_M (Bvar z) (Mvar n3) (Mvar n4))(m2:= m2) in H1.
simpl in H1; rewrite <- beq_nat_refl in H1 ;
try rewrite H5 in H1; try rewrite H6 in H1; try rewrite H7 in H1; try rewrite H8 in H1.
rewrite  notocc_bolmm with (n1 :=z ) (n2:=n5) (b := b) (m1:= (Mvar n1))(m2:= m1) in H1. 
rewrite  notocc_bolmm with (n1 :=z ) (n2:=n6) (b := b) (m1:= (Mvar n4))(m2:= m2) in H1.
simpl in H1.
try rewrite H5 in H1; try rewrite H6 in H1; try rewrite H7 in H1; try rewrite H8 in H1.
rewrite H1. reflexivity.

inversion H4; apply andb_prop in H4; inversion H4 ;apply andb_prop in H10 ;inversion H10;
try rewrite H3; try rewrite H11; reflexivity. 

inversion H4; apply andb_prop in H4; inversion H4 ;apply andb_prop in H10 ;inversion H10;
try rewrite H3; try rewrite H11; reflexivity. 

inversion H4; apply andb_prop in H4; inversion H4 ;apply andb_prop in H10 ;inversion H10;
try rewrite H3; try rewrite H11; reflexivity. 
inversion H4; apply andb_prop in H4; inversion H4 ;apply andb_prop in H10 ;inversion H10;
try rewrite H3; try rewrite H11; reflexivity. 
Qed.




Theorem Ex9msg_bol:  forall (b1 b2: Bool )(n n1 n2 n3 n4 n5 n6 :nat),  (notoccur_nlist n [n1 ; n2 ; n3;n4] = true)  /\ (notoccur_blist n [b1 ; b2]  = true) -> ( if_then_else_B (Bvar n) ([[n5:=  (if_then_else_M (Bvar n) (Mvar n1) (Mvar n2))]] b1)
([[n6:=  (if_then_else_M (Bvar n) (Mvar n3) (Mvar n4))]] b2)) ## (if_then_else_B (Bvar n)  ( [[n5:= (Mvar n1)]] b1) ([[n6:= (Mvar n4)]] b2)) .
Proof.
intros.
inversion H.
(************notoccn_nlist n [n1; n2; n3; n4] = true -> n<> n1/\ n<> n2/\ n<> n3/\ n<> n4 ********************)
unfold notoccur_nlist in H0.
assert(H2: beq_nat n1 n  = false).
destruct(beq_nat n1 n).
-inversion H0.
-reflexivity.
-assert(H3: beq_nat n2 n  = false).
+destruct(beq_nat n2 n).
{inversion H0. rewrite H2. reflexivity. }
{reflexivity. }
+assert(H4: beq_nat n3 n  = false).
destruct(beq_nat n3 n).
inversion H0.
rewrite H2.
rewrite H3.

reflexivity.
reflexivity.

assert(H5 : beq_nat n4 n  = false).
destruct(beq_nat n4 n).
inversion H0.
rewrite H2.
rewrite H3.
rewrite H4.
reflexivity.
reflexivity.
(***apply beq_nat_false_iff in H2.
apply beq_nat_false_iff in H3.
apply beq_nat_false_iff in H4.
apply beq_nat_false_iff in H5.***)
(***********************)


rewrite IFEVAL_B with(n:=n)(b1:=  [[n5 := if_then_else_M (Bvar n) (Mvar n1) (Mvar n2)]](b1)) (b2:=  [[n6 := if_then_else_M (Bvar n) (Mvar n3) (Mvar n4)]](b2)).
rewrite  notocc_bolmb with (n1 :=n ) (n2:=n5) (b := TRue) (m:= if_then_else_M (Bvar n) (Mvar n1) (Mvar n2))(b1:= b1).
(**destruct Boolbolbol with (n:=n)(b:= TRue)(n1:= n5)(b1:= if_then_else_B (Bvar n) (Bvar n1) (Bvar n2)) (b2:=b1).**)
 simpl.
rewrite <- beq_nat_refl.

rewrite IFTRUE_M .
try rewrite H2; try rewrite H3; try rewrite H4; try rewrite H5.
simpl.
rewrite  notocc_bolmb with (n1 :=n ) (n2:=n6) (b := FAlse) (m:= if_then_else_M (Bvar n) (Mvar n3) (Mvar n4))(b1:= b2).
(*destruct Boolblbl with (n:=n)(b:= FAlse)(n1:= n6)(b1:= if_then_else_B (Bvar n) (Bvar n3) (Bvar n4)) (b2:=b2).*)
simpl.
rewrite <- beq_nat_refl.
try rewrite H2; try rewrite H3; try rewrite H4; try rewrite H5.
rewrite IFFALSE_M. reflexivity.
inversion H1; apply andb_prop in H7;inversion H7;rewrite H8; rewrite H6; apply andb_prop in H8; inversion H8;
try rewrite H9; reflexivity.
inversion H1;apply andb_prop in H7;inversion H7;rewrite H8; rewrite H6; apply andb_prop in H8; inversion H8;
try rewrite H9; reflexivity.
Qed.


Theorem Ex9msg_bol1: forall (b b1 b2: Bool )(n1 n2 n3 n4 n5 n6 :nat) , ( if_then_else_B b ([[n5:=  (if_then_else_M b (Mvar n1) (Mvar n2))]] b1)
([[n6:=  (if_then_else_M b (Mvar n3) (Mvar n4))]] b2)) ## (if_then_else_B b  ( [[n5:= (Mvar n1)]] b1) ([[n6:= (Mvar n4)]] b2)) .
Proof.
intros.
assert(H:  exists n:nat, (notoccur_nlist n [n1 ; n2;n3;n4] = true ) /\(notoccur_blist n [ b1 ; b2  ] = true)  ).
pose proof (existsn_Mlist).
apply existsn_Blist with (m1:=4) (nl := [n1 ; n2;n3;n4]) (bl := [ b1 ; b2 ])(m2:=2).
inversion H as [z H1].
inversion H1.
unfold notoccur_nlist in H0.
inversion H2.
assert(H5: beq_nat n1 z = false).
destruct(beq_nat n1 z).
inversion H1.
rewrite <- H0.
reflexivity.
reflexivity.
assert(H6: beq_nat n2 z =false).
destruct(beq_nat n2 z).
rewrite H5 in H0.
simpl in H0.
rewrite <- H0. reflexivity.
reflexivity.
assert(H7: beq_nat n3 z = false).
destruct (beq_nat n3 z).
rewrite H5 in H0.
rewrite H6 in H0. simpl in H0. rewrite <- H0. reflexivity. reflexivity.
assert(H8: beq_nat n4 z = false).
destruct (beq_nat n4 z).
simpl in H0.
rewrite H5 in H0.
rewrite H6 in H0.
rewrite H7 in H0.
rewrite <- H0. try  repeat reflexivity. reflexivity.
apply Ex9msg_bol with (n5:= n5)(n6:=n6)in H1.
apply Forall_ELM_EVAL_B with (n:=z) (b:= b)in H1.
simpl in H1.
(**destruct Boolblbl with (n:=z)(n1:= n5)(b:=b)(b1:= if_then_else_B (Bvar z) (Bvar n1) (Bvar n2))(b2:= b1) in H1.**)
 rewrite  notocc_bolmb with (n1 :=z ) (n2:=n5) (b := b) (m := if_then_else_M (Bvar z) (Mvar n1) (Mvar n2))(b1:= b1) in H1.
rewrite <- beq_nat_refl in H1.
simpl in H1.
rewrite <- beq_nat_refl in H1.
try rewrite H5 in H1; try rewrite H6 in H1; try rewrite H7 in H1; try rewrite H8 in H1.
rewrite  notocc_bolmb with (n1 :=z ) (n2:=n6) (b := b) (m:= if_then_else_M (Bvar z) (Mvar n3) (Mvar n4))(b1:= b2) in H1.
simpl in H1; rewrite <- beq_nat_refl in H1 ;
try rewrite H5 in H1; try rewrite H6 in H1; try rewrite H7 in H1; try rewrite H8 in H1.
rewrite  notocc_bolmb with (n1 :=z ) (n2:=n5) (b := b) (m:= (Mvar n1))(b1:= b1) in H1. 
rewrite  notocc_bolmb with (n1 :=z ) (n2:=n6) (b := b) (m:= (Mvar n4))(b1:= b2) in H1.
simpl in H1.
try rewrite H5 in H1; try rewrite H6 in H1; try rewrite H7 in H1; try rewrite H8 in H1.
rewrite H1. reflexivity.
inversion H4; apply andb_prop in H4; inversion H4 ;apply andb_prop in H10 ;inversion H10;
try rewrite H3; try rewrite H11; reflexivity. 
inversion H4; apply andb_prop in H4; inversion H4 ;apply andb_prop in H10 ;inversion H10;
try rewrite H3; try rewrite H11; reflexivity. 
inversion H4; apply andb_prop in H4; inversion H4 ;apply andb_prop in H10 ;inversion H10;
try rewrite H3; try rewrite H11; reflexivity. 
inversion H4; apply andb_prop in H4; inversion H4 ;apply andb_prop in H10 ;inversion H10;
try rewrite H3; try rewrite H11; reflexivity. 
Qed.
