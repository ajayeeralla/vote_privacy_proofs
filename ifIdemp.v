Require Export ifTf.

(** This library defines a theorem [IFIDEMP] and its proof. Notice that we use [#] (resp. [##]) for [message] (resp. [Bool]) in lieu of [=].

 [if b then (if b then x1 else y1) else (if b then x2 else y2) # if b then x1 else y2] *)

Theorem IFIDEMP_B : forall (n: nat)(b1 b2 b3 b4 : Bool), (IF (Bvar n) then (IF (Bvar n) then b1 else b2) else (IF (Bvar n) then b3 else b4)) ## (IF (Bvar n) then b1 else b4).
Proof.
intros n b1 b2 b3 b4.
rewrite IFEVAL_B with (b1:= IF (Bvar n) then b1 else b2)(b2 := (IF (Bvar n) then b3 else b4)) .
simpl.
rewrite <-beq_nat_refl.
rewrite IFTRUE_B.
rewrite IFFALSE_B.
rewrite IFEVAL_B with(b2:=b4).
reflexivity.               
Qed.
 
Theorem IFIDEMP_M : forall (n: nat)(x1 x2 y1 y2 : message),  (If (Bvar n) then (If (Bvar n) then x1 else y1) else (If (Bvar n) then x2 else y2)) # (If (Bvar n) then x1 else y2).
Proof.
intros n x1 x2 y1 y2 .
rewrite IFEVAL_M with (t1:= If (Bvar n) then x1 else y1)(t2 := (If (Bvar n) then x2 else y2)) .
simpl.
rewrite <-beq_nat_refl.
rewrite IFTRUE_M.
rewrite IFFALSE_M. 
rewrite IFEVAL_M with (t2:=y2).
reflexivity.
Qed.
 