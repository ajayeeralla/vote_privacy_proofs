Require Export ifIdemp.

(** This library defines several theorems of [IFMORPH] and the proofs. Notice that we use [#] (resp. [##]) for [message] (resp. [Bool]) in lieu of [=].
 
[(if b then (if b' then x else y) else z) = (if b' then (if b then x else z) else (if b then y else z))]. *)
 
Theorem IFMORPH_M1: forall ( x y z : message) (n1 n2:nat),
(If (Bvar n2) then (If (Bvar n1) then x else y) else z) # (If (Bvar n1) then (If (Bvar n2) then x else z) else (If (Bvar n2) then y  else z) ).
Proof.
intros.
rewrite <- IFSAME_M with (b:= (Bvar n1)) (x:= (If (Bvar n2) then (If (Bvar n1) then x else y) else z)).
rewrite IFEVAL_M.
simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_M.
rewrite IFFALSE_M.
rewrite IFEVAL_M with (t1:= (If (Bvar n2) then x else z))(t2:= (If (Bvar n2) then y else z)).
simpl.
reflexivity.
Qed.

Theorem IFMORPH_B1: forall ( b b1 b2 : Bool) (n1 n2:nat) ,
 (IF (Bvar n2) then (IF (Bvar n1) then b else b1) else b2)  ## (IF (Bvar n1) then (IF (Bvar n2) then b else b2) else (IF  (Bvar n2) then b1 else b2)).
Proof.
intros.
rewrite <- IFSAME_B with (b:= (Bvar n1)) (b1:= (IF (Bvar n2) then (IF (Bvar n1) then b else b1) else b2)).
rewrite IFEVAL_B.
simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_B.
rewrite IFFALSE_B.
rewrite IFEVAL_B with (n:=n1)(b1:= (IF (Bvar n2) then b else b2))(b2:= (IF (Bvar n2) then b1 else b2)).
simpl.
reflexivity.
Qed.
(**For a function [f:Bool -> Bool-> Bool], we have [f(if b then x else y, z , z1) = if b then f(x,z,z1) else f(x,y,z1)] *)

Theorem IFMORPH_B2: forall (n:nat)(b1 b2 b3 b4 : Bool) , 
(IF (IF (Bvar n) then b1 else b2) then b3 else b4)  ##  (IF (Bvar n) then (IF b1 then b3 else b4) else (IF b2 then b3 else b4)).
Proof.
intros.
pose proof (IFSAME_B).
rewrite <- IFSAME_B with (b:= (Bvar n)) (b1:=(IF (IF (Bvar n) then b1 else b2) then b3 else b4)).
pose proof(IFEVAL_B).
rewrite IFEVAL_B.
simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_B.
rewrite IFFALSE_B.
rewrite IFEVAL_B with (b1 := (IF b1 then b3 else b4))(b2:= (IF b2 then b3 else b4)).
simpl.
reflexivity.
Qed.
(**For a function [f: message -> message -> Bool], we have [f(if b then x else y, z , z1) = if b then f(x,z,z1) else f(x,y,z1)] *)
Theorem IFMORPH_M2: forall (n:nat)(b1 b2 :Bool)(y z : message), 
 (If (IF (Bvar n) then b1 else b2) then y else z)  #(If (Bvar n) then (If b1 then y else z ) else (If b2 then y else z)).
Proof.
intros.
rewrite <- IFSAME_M with (b:=(Bvar n))(x:= If (IF (Bvar n) then b1 else b2) then y else z).
rewrite IFEVAL_M.
simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_B.
rewrite IFFALSE_B.
rewrite IFEVAL_M with (t1:=  (If b1 then y else z))(t2:= (If b2 then y else z)).
simpl.
reflexivity.
Qed.

(** For a function [f: Bool -> Bool -> Bool], we have [f(if b then x else y, z) = if b then f(x,z) else f(y,z) ] *)

Theorem IFMORPH_B3: forall  (n n1 n2 n3 :nat), ( eqb (IF (Bvar n) then (Bvar n1) else (Bvar n2)) (Bvar n3)) ##  (IF (Bvar n) then (eqb (Bvar n1) (Bvar n3)) else (eqb (Bvar n2) (Bvar n3))).
Proof.
intros.
rewrite <- IFSAME_B with (b:=(Bvar n))( b1:= eqb (IF (Bvar n) then (Bvar n1) else (Bvar n2)) (Bvar n3)).
rewrite IFEVAL_B.
simpl. rewrite <- beq_nat_refl.
rewrite IFTRUE_B.
rewrite IFFALSE_B.
rewrite IFEVAL_B with (b1:= (eqb (Bvar n1) (Bvar n3)))(b2:= (eqb (Bvar n2) (Bvar n3))).
simpl.
reflexivity.
Qed.

Theorem IFMORPH_M3: forall  (n n1 n2 n3 :nat), ( eqm (If (Bvar n) then (Mvar n1) else (Mvar n3))  (If (Bvar n) then (Mvar n2) else (Mvar n3))) ## ( IF (Bvar n) then (eqm (Mvar n1)  (If (Bvar n) then (Mvar n2) else (Mvar n3))) else (eqm (Mvar n3)  (If (Bvar n) then (Mvar n2) else (Mvar n3)))). 
Proof.
intros.
rewrite <- IFSAME_B with (b:=(Bvar n))( b1:= eqm (If (Bvar n) then (Mvar n1) else (Mvar n3))  (If (Bvar n) then (Mvar n2) else (Mvar n3))).
rewrite IFEVAL_B.
simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_M.
rewrite IFFALSE_M .
rewrite IFTRUE_M.
rewrite IFFALSE_M.
rewrite IFEVAL_B with (b1:= (eqm (Mvar n1) (If (Bvar n) then (Mvar n2) else (Mvar n3))))(b2:= (eqm (Mvar n3) (If (Bvar n) then (Mvar n2) else (Mvar n3)))).
simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_M.
rewrite IFFALSE_M.
reflexivity.
Qed.

Theorem IFMORPH_M5 : forall (n1 n2 n3 :nat) (m1 m2 m3 m4: message),  (If (Bvar n1) then (If (Bvar n2) then m1 else m2) else (If (Bvar n3) then m3 else m4)) # (If (Bvar n2) then (If (Bvar n1) then m1 else (If (Bvar n3) then m3 else m4)) else (If (Bvar n1) then m2 else (If (Bvar n3) then m3 else m4))).
Proof. intros. 
pose proof(IFSAME_M (Bvar n2) (If (Bvar n1) then (If (Bvar n2) then m1 else m2) else (If (Bvar n3) then m3 else m4))).
rewrite IFEVAL_M with (n:= n2) (t1:= (If (Bvar n1) then (If (Bvar n2) then m1 else m2) else (If (Bvar n3) then m3 else m4))) (t2 := (If (Bvar n1) then (If (Bvar n2) then m1 else m2) else (If (Bvar n3) then m3 else m4))) in H.
simpl in H.
repeat rewrite <- beq_nat_refl in H.
rewrite <-H. 
rewrite IFEVAL_M with (n:= n2) (t1:= (If (Bvar n1) then m1 else (If (Bvar n3) then m3 else m4))) (t2 := (If (Bvar n1) then m2 else (If (Bvar n3) then m3 else m4))).
simpl. rewrite  IFTRUE_M, IFFALSE_M.
reflexivity. Qed.

Theorem IFMORPH_M6 : forall(n1 n2 :nat) (m1 m2 m3:message), (If (Bvar n1) then m1 else (If (Bvar n2) then m2 else m3)) # (If (Bvar n2) then (If (Bvar n1) then m1 else m2) else (If (Bvar n1) then m1 else m3)).
Proof. intros. pose proof(IFSAME_M (Bvar n2)  (If (Bvar n1) then m1 else (If (Bvar n2) then m2 else m3))).
rewrite IFEVAL_M in H.
simpl in H. repeat rewrite <- beq_nat_refl in H.
rewrite  IFTRUE_M, IFFALSE_M in H.
rewrite <-H. clear H.
rewrite IFEVAL_M with (t1:= (If (Bvar n1) then m1 else m2)).
simpl. reflexivity. Qed.
(*
Axiom IFMORPH_B4: forall  (n1:nat) (b1 b2 b3:Bool), (IF (Bvar n1) b1 (IF (Bvar (n1+1)) b2 b3))  ## (IF (Bvar (n1+1)) (IF (Bvar n1) b1 b2) (IF (Bvar n1) b1 b3)) .
*)

Theorem IFMORPH_M4 : forall (n1:nat) (m1 m2 m3 : message), (If (Bvar n1) then m1 else (If (Bvar (n1+1)) then m2 else m3) ) # (If (Bvar (n1+1)) then (If (Bvar n1) then m1 else m2) else (If (Bvar n1) then m1 else m3)).
Proof. 
intros.
rewrite <- IFSAME_M with (b:= (Bvar (n1+1))) (x:= (If (Bvar n1) then m1 else (If (Bvar (n1+1)) then m2 else m3))).
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
 rewrite IFEVAL_M with (t1:=(If (Bvar n1) then m1 else m2))(t2:= (If (Bvar n1) then m1 else m3)).
simpl.
rewrite H.
reflexivity.
Qed.

 