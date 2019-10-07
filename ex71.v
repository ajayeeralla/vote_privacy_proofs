
(************************************************************************)
(* Copyright (c) 2015-2019, Ajay Kumar Eeralla                          *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(************************************************************************)    

Require Export indEq.

(** This library defines a theorem and its proof. Notice that we use [#] (resp. [##]) for [message] (resp. [Bool]) in lieu of [=] .

[ if b then t1[[if b then x1 else y1]] else t2[[if b then x2 else y2]] = if b then t1[[x1]] else t2[[y2]] ] *)

(*Bool in Bool*)

(** tactic Fr_pf1 *)
Ltac Fr_pf1 := 
repeat match goal with 
| [ |- beq_nat ?X ?Y = ?Z] => destruct (beq_nat X Y) ;  match goal with | [H1: context [ if beq_nat ?X' ?Y' then ?Z' else ?Z''] |- _ ] =>  simpl in H1; repeat rewrite <- beq_nat_refl in H1 ; simpl in H1;  symmetry  end end; try assumption ; try reflexivity;
   repeat match goal with 
          | [ H : beq_nat ?X ?Y = _ |- _ ] =>  match goal with | [H1: context [ if beq_nat ?X ?Y then _ else _ ] |- _ ] =>  rewrite H in H1;  simpl in H1 end end; try assumption ; try reflexivity.

 

Fixpoint notoccur_mlist (x:nat) {n} (ml : ilist message n):bool :=
  match ml with
    | [] => true
    | h: ml1 => (andb (negb(occur_name_msg x h)) (notoccur_mlist x ml1))
  end.

(** Check if absence of a variable in [ilist] *)

Fixpoint notoccur_blist {m:nat}(x:nat) (ml : ilist Bool m):bool :=
  match ml with
    | [] => true
    | h : ml1 => (andb (negb(occur_name_bol x h)) (notoccur_blist x ml1))
  end.
(** Check if an element occurs in [ilist] *)

 Fixpoint notoccur_nlist {n:nat}(a:nat) (l:ilist nat n) : bool :=
    match l with
      | [] => true
      | h:t =>   if (beq_nat h a) then false else (notoccur_nlist a t)
    end.

 Axiom existsn_Blist : forall (m1 m2 :nat) (nl : ilist nat m1)(bl:ilist Bool m2), exists n , (notoccur_nlist n nl = true) /\ (notoccur_blist n bl = true).
 
Axiom existsn_Mlist: forall (m1 m2 :nat) (nl : ilist nat m1)(ml:ilist message m2), exists n , (notoccur_nlist n nl = true) /\ (notoccur_mlist n ml = true).

Theorem Ex9bol_bol: forall (b1 b2: Bool )(n n1 n2 n3 n4 n5 n6 :nat),  (notoccur_nlist n [n1 , n2 , n3,n4] = true)  /\ (notoccur_blist n [b1 , b2]  = true) 
                     ->  (IF (Bvar n) then ([n5:= (IF (Bvar n) then (Bvar n1) else (Bvar n2))] b1) else ([n6:=  (IF (Bvar n) then (Bvar n3) else (Bvar n4))] b2))
                      ##  (IF (Bvar n) then ([n5:= (Bvar n1)] b1) else ([n6:= (Bvar n4)] b2)).
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
rewrite IFEVAL_B with(n:=n)(b1:=  [n5 := IF (Bvar n) then (Bvar n1) else (Bvar n2)](b1)) (b2:=  [n6 := IF (Bvar n) then (Bvar n3) else (Bvar n4)](b2)).
rewrite  notocc_bolbb with (n1 :=n ) (n2:=n5) (b := TRue) (b1:= IF (Bvar n) then (Bvar n1) else (Bvar n2))(b2:= b1).
 simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_B .
try rewrite H2; try rewrite H3; try rewrite H4; try rewrite H5.
simpl.
rewrite  notocc_bolbb with (n1 :=n) (n2:=n6) (b := FAlse) (b1:= IF (Bvar n) then (Bvar n3) else (Bvar n4))(b2:= b2).
simpl.
rewrite <- beq_nat_refl.
try rewrite H2; try rewrite H3; try rewrite H4; try rewrite H5.
rewrite IFFALSE_B. reflexivity.
Ltac aply_andb_prop :=
  repeat match goal with
|[H: ((negb ?X) && _ = true)%bool |- _] => apply andb_prop in H; inversion H
end.
Ltac red_occ_n_msg:=
try match goal with
|[H: notoccur_mlist ?X _ = _ |- occur_name_msg ?X _ = _ ] => simpl in H; aply_andb_prop
       end.

Ltac red_occ_n_bol:=
try match goal with
|[H: notoccur_blist ?X _ = _ |- occur_name_bol ?X _ = _ ] => simpl in H; aply_andb_prop
end. 

Ltac aply_negb_true :=
  repeat match goal with
  | [H: negb ?X = true |- _ ] => apply Bool.negb_true_iff in H; try auto
         end.
Ltac red_occ_n := 
red_occ_n_msg; red_occ_n_bol; aply_negb_true.
try red_occ_n. red_occ_n.
Qed.


Theorem Ex9bol_bol1: forall (b b1 b2: Bool )( n1 n2 n3 n4 n5 n6 :nat),   (IF b then ([n5:= (IF b then (Bvar n1) else (Bvar n2))] b1) else ([n6:=  (IF b then (Bvar n3) else (Bvar n4))] b2))
                      ##  (IF b then ([n5:= (Bvar n1)] b1) else  ([n6:= (Bvar n4)] b2)).

Proof.
intros.
assert(H:  exists n:nat, (notoccur_nlist n [n1 , n2,n3,n4] = true ) /\(notoccur_blist n [ b1 , b2  ] = true)  ).
apply existsn_Blist with (m1:=4) (nl := [n1 , n2,n3,n4]) (bl := [ b1 , b2 ])(m2:=2).
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
(**destruct Boolblbl with (n:=z)(n1:= n5)(b:=b)(b1:= ifb (Bvar z) (Bvar n1) (Bvar n2))(b2:= b1) in H1.**)
 rewrite  notocc_bolbb with (n1 :=z ) (n2:=n5) (b := b) (b1:= IF (Bvar z) then (Bvar n1) else (Bvar n2))(b2:= b1) in H1.
rewrite <- beq_nat_refl in H1.
simpl in H1.
rewrite <- beq_nat_refl in H1.
try rewrite H5 in H1; try rewrite H6 in H1; try rewrite H7 in H1; try rewrite H8 in H1.
rewrite  notocc_bolbb with (n1 :=z ) (n2:=n6) (b := b) (b1:= IF (Bvar z) then (Bvar n3) else (Bvar n4))(b2:= b2) in H1.
simpl in H1; rewrite <- beq_nat_refl in H1 ;
try rewrite H5 in H1; try rewrite H6 in H1; try rewrite H7 in H1; try rewrite H8 in H1.
rewrite  notocc_bolbb with (n1 :=z ) (n2:=n5) (b := b) (b1:= (Bvar n1))(b2:= b1) in H1. 
rewrite  notocc_bolbb with (n1 :=z ) (n2:=n6) (b := b) (b1:= (Bvar n4))(b2:= b2) in H1.
simpl in H1.
try rewrite H5 in H1; try rewrite H6 in H1; try rewrite H7 in H1; try rewrite H8 in H1.
rewrite H1. reflexivity.
red_occ_n.
red_occ_n.
red_occ_n.
red_occ_n.
Qed.





Theorem Ex9bol_msg: forall (m1 m2: message )(n n1 n2 n3 n4 n5 n6 :nat),  (notoccur_nlist n [n1 , n2 , n3,n4] = true)  /\ (notoccur_mlist n [m1 , m2]  = true) 
                     -> (If  (Bvar n) then ((n5:=  (IF (Bvar n) then (Bvar n1) else (Bvar n2))) m1) else
((n6:=  (IF (Bvar n) then (Bvar n3) else (Bvar n4))) m2)) #  (If (Bvar n) then ((n5:= (Bvar n1)) m1) else ((n6:= (Bvar n4)) m2)).
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
rewrite IFEVAL_M with  (t1:=  (n5 := IF (Bvar n) then (Bvar n1) else (Bvar n2))(m1)) (t2:=  (n6 := IF (Bvar n) then (Bvar n3)else (Bvar n4))(m2)).
rewrite notocc_bolbm with (n1 := n) (b := TRue) (n2:= n5) (b1 := (IF (Bvar n) then (Bvar n1) else (Bvar n2))) (m:= m1).
simpl ;rewrite <- beq_nat_refl.
try rewrite H2; try rewrite H3; try rewrite H4; try rewrite H5.
rewrite IFTRUE_B .
rewrite notocc_bolbm with (n1 := n) (b := FAlse) (n2:= n6) (b1 := (IF (Bvar n) then (Bvar n3) else (Bvar n4))) (m:= m2).
simpl ;rewrite <- beq_nat_refl.
try rewrite H2; try rewrite H3; try rewrite H4; try rewrite H5.
rewrite IFFALSE_B .
reflexivity.
red_occ_n.
red_occ_n.
Qed.

Theorem Ex9bol_msg1: forall (b : Bool ) (m1 m2 : message)(n1 n2 n3 n4 n5 n6:nat) ,  (If b then ((n5:=  (IF b then (Bvar n1) else (Bvar n2))) m1) else
((n6:=  (IF b then (Bvar n3) else (Bvar n4))) m2)) #  (If b then ( (n5:= (Bvar n1)) m1) else ((n6:= (Bvar n4)) m2) ) .
Proof.
intros.
assert(H:  exists n:nat, (notoccur_nlist n [n1 , n2,n3,n4] = true ) /\(notoccur_mlist n [ m1 , m2  ] = true)  ).

apply existsn_Mlist with (m1:=4) (nl := [n1 , n2,n3,n4]) (ml := [ m1 , m2 ])(m2:=2).
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

(**destruct Boolblbl with (n:=z)(n1:= n5)(b:=b)(b1:= IF (Bvar z) (Bvar n1) (Bvar n2))(b2:= b1) in H1.**)
 rewrite  notocc_bolbm with (n1 :=z ) (n2:=n5) (b := b) (b1:= IF (Bvar z) then (Bvar n1) else (Bvar n2))(m:= m1) in H1.
rewrite <- beq_nat_refl in H1.

simpl in H1.
rewrite <- beq_nat_refl in H1.
try rewrite H5 in H1; try rewrite H6 in H1; try rewrite H7 in H1; try rewrite H8 in H1.

rewrite  notocc_bolbm with (n1 :=z ) (n2:=n6) (b := b) (b1:= IF (Bvar z) then (Bvar n3) else (Bvar n4))(m:= m2) in H1.
simpl in H1; rewrite <- beq_nat_refl in H1 ;
try rewrite H5 in H1; try rewrite H6 in H1; try rewrite H7 in H1; try rewrite H8 in H1.
rewrite  notocc_bolbm with (n1 :=z ) (n2:=n5) (b := b) (b1:= (Bvar n1))(m:= m1) in H1. 
rewrite  notocc_bolbm with (n1 :=z ) (n2:=n6) (b := b) (b1:= (Bvar n4))(m:= m2) in H1.
simpl in H1.
try rewrite H5 in H1; try rewrite H6 in H1; try rewrite H7 in H1; try rewrite H8 in H1.
rewrite H1. reflexivity.
red_occ_n.
red_occ_n.
red_occ_n.
red_occ_n.

Qed.


(****message in message*******************)

Theorem Ex9msg_msg: forall (m1 m2: message )(n n1 n2 n3 n4 n5 n6 :nat),  (notoccur_nlist n [n1 , n2 , n3,n4] = true)  /\ (notoccur_mlist n [m1 , m2]  = true) 
                     ->  (If (Bvar n) then (submsg_msg n5  (If (Bvar n) then (Mvar n1) else (Mvar n2)) m1) else
(submsg_msg n6 (If (Bvar n) then (Mvar n3) else (Mvar n4)) m2 ) )  #(If  (Bvar n) then  (submsg_msg n5 (Mvar n1) m1) else (submsg_msg n6 (Mvar n4) m2)) .
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
rewrite IFEVAL_M with  (t1:=  {{n5 := (If (Bvar n) then (Mvar n1) else (Mvar n2))}}(m1)) (t2:=  {{n6 :=  (If (Bvar n) then (Mvar n3) else (Mvar n4))}}(m2)).
rewrite notocc_bolmm with (n1 := n) (b := TRue) (n2:= n5) (m1 := If (Bvar n) then (Mvar n1) else (Mvar n2)) (m2:= m1).
simpl ;rewrite <- beq_nat_refl.
try rewrite H2; try rewrite H3; try rewrite H4; try rewrite H5.
rewrite IFTRUE_M .
rewrite notocc_bolmm with (n1 := n) (b := FAlse) (n2:= n6) (m1 := If (Bvar n) then (Mvar n3) else (Mvar n4)) (m2:= m2).
simpl ;rewrite <- beq_nat_refl.
try rewrite H2; try rewrite H3; try rewrite H4; try rewrite H5.
rewrite IFFALSE_M .
reflexivity.
red_occ_n.
red_occ_n.

Qed.

Theorem Ex9msg_msg1: forall (m1 m2: message )(b:Bool)(n1 n2 n3 n4 n5 n6 :nat) , (If b then (submsg_msg n5  (If b then (Mvar n1) else (Mvar n2) ) m1) else
(submsg_msg n6 (If b then (Mvar n3) else (Mvar n4)) m2 ) ) #  ( If b then (submsg_msg n5 (Mvar n1) m1) else (submsg_msg n6 (Mvar n4) m2) ) .

Proof.


intros.
assert(H:  exists n:nat, (notoccur_nlist n [n1 , n2,n3,n4] = true ) /\(notoccur_mlist n [ m1 , m2  ] = true)  ).
pose proof (existsn_Mlist).
apply existsn_Mlist with (m1:=4) (nl := [n1 , n2,n3,n4]) (ml := [ m1 , m2 ])(m2:=2).
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

(**destruct Boolblbl with (n:=z)(n1:= n5)(b:=b)(b1:= IF (Bvar z) (Bvar n1) (Bvar n2))(b2:= b1) in H1.**)
 rewrite  notocc_bolmm with (n1 :=z ) (n2:=n5) (b := b) (m1 := If (Bvar z) then (Mvar n1) else (Mvar n2))(m2:= m1) in H1.
rewrite <- beq_nat_refl in H1.

simpl in H1.
rewrite <- beq_nat_refl in H1.
try rewrite H5 in H1; try rewrite H6 in H1; try rewrite H7 in H1; try rewrite H8 in H1.

rewrite  notocc_bolmm with (n1 :=z ) (n2:=n6) (b := b) (m1:= If (Bvar z) then (Mvar n3) else (Mvar n4))(m2:= m2) in H1.
simpl in H1; rewrite <- beq_nat_refl in H1 ;
try rewrite H5 in H1; try rewrite H6 in H1; try rewrite H7 in H1; try rewrite H8 in H1.
rewrite  notocc_bolmm with (n1 :=z ) (n2:=n5) (b := b) (m1:= (Mvar n1))(m2:= m1) in H1. 
rewrite  notocc_bolmm with (n1 :=z ) (n2:=n6) (b := b) (m1:= (Mvar n4))(m2:= m2) in H1.
simpl in H1.
try rewrite H5 in H1; try rewrite H6 in H1; try rewrite H7 in H1; try rewrite H8 in H1.
rewrite H1. reflexivity.

red_occ_n.
red_occ_n.
red_occ_n.
red_occ_n.
Qed.




Theorem Ex9msg_bol:  forall (b1 b2: Bool )(n n1 n2 n3 n4 n5 n6 :nat),  (notoccur_nlist n [n1 , n2 ,n3,n4] = true)  /\ (notoccur_blist n [b1 , b2]  = true) -> ( IF (Bvar n) then ([[n5:=  (If (Bvar n) then (Mvar n1) else (Mvar n2))]] b1) else
([[n6:=  (If (Bvar n) then (Mvar n3) else (Mvar n4))]] b2)) ## (IF (Bvar n) then ([[n5:= (Mvar n1)]] b1) else ([[n6:= (Mvar n4)]] b2)) .
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


rewrite IFEVAL_B with(n:=n)(b1:=  [[n5 := If (Bvar n) then (Mvar n1) else (Mvar n2)]](b1)) (b2:=  [[n6 := If (Bvar n) then (Mvar n3) else (Mvar n4)]](b2)).
rewrite  notocc_bolmb with (n1 :=n ) (n2:=n5) (b := TRue) (m:= If (Bvar n) then (Mvar n1) else (Mvar n2))(b1:= b1).
(**destruct Boolbolbol with (n:=n)(b:= TRue)(n1:= n5)(b1:= IF (Bvar n) (Bvar n1) (Bvar n2)) (b2:=b1).**)
 simpl.
rewrite <- beq_nat_refl.

rewrite IFTRUE_M .
try rewrite H2; try rewrite H3; try rewrite H4; try rewrite H5.
simpl.
rewrite  notocc_bolmb with (n1 :=n ) (n2:=n6) (b := FAlse) (m:= If (Bvar n) then (Mvar n3) else (Mvar n4))(b1:= b2).
(*destruct Boolblbl with (n:=n)(b:= FAlse)(n1:= n6)(b1:= IF (Bvar n) (Bvar n3) (Bvar n4)) (b2:=b2).*)
simpl.
rewrite <- beq_nat_refl.
try rewrite H2; try rewrite H3; try rewrite H4; try rewrite H5.
rewrite IFFALSE_M. reflexivity.
red_occ_n.
red_occ_n.
Qed.


Theorem Ex9msg_bol1: forall (b b1 b2: Bool )(n1 n2 n3 n4 n5 n6 :nat) , ( IF b then ([[n5:=  (If b then (Mvar n1) else (Mvar n2))]] b1) else
([[n6:=  (If b then (Mvar n3) else (Mvar n4))]] b2)) ## (IF b then ( [[n5:= (Mvar n1)]] b1) else ([[n6:= (Mvar n4)]] b2)).
Proof.
intros.
assert(H:  exists n:nat, (notoccur_nlist n [n1,n2,n3,n4] = true ) /\(notoccur_blist n [ b1 , b2  ] = true)  ).
pose proof (existsn_Mlist).
apply existsn_Blist with (m1:=4) (nl := [n1 , n2,n3,n4]) (bl := [ b1 , b2 ])(m2:=2).
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
(**destruct Boolblbl with (n:=z)(n1:= n5)(b:=b)(b1:= IF (Bvar z) (Bvar n1) (Bvar n2))(b2:= b1) in H1.**)
 rewrite  notocc_bolmb with (n1 :=z ) (n2:=n5) (b := b) (m := If (Bvar z) then (Mvar n1) else (Mvar n2))(b1:= b1) in H1.
rewrite <- beq_nat_refl in H1.
simpl in H1.
rewrite <- beq_nat_refl in H1.
try rewrite H5 in H1; try rewrite H6 in H1; try rewrite H7 in H1; try rewrite H8 in H1.
rewrite  notocc_bolmb with (n1 :=z ) (n2:=n6) (b := b) (m:= If (Bvar z) then (Mvar n3) else (Mvar n4))(b1:= b2) in H1.
simpl in H1; rewrite <- beq_nat_refl in H1 ;
try rewrite H5 in H1; try rewrite H6 in H1; try rewrite H7 in H1; try rewrite H8 in H1.
rewrite  notocc_bolmb with (n1 :=z ) (n2:=n5) (b := b) (m:= (Mvar n1))(b1:= b1) in H1. 
rewrite  notocc_bolmb with (n1 :=z ) (n2:=n6) (b := b) (m:= (Mvar n4))(b1:= b2) in H1.
simpl in H1.
try rewrite H5 in H1; try rewrite H6 in H1; try rewrite H7 in H1; try rewrite H8 in H1.
rewrite H1. reflexivity.
red_occ_n.
red_occ_n.
red_occ_n.
red_occ_n.
Qed.


