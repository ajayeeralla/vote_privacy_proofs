(************************************************************************)
(* Copyright (c) 2015-2019, Ajay Kumar Eeralla                          *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(************************************************************************)    

Require Export eqm.

(** This library defines a theorem that states, 

[if EQ(x1 , x2) then x1 else y = if EQ(x1 ,x2) then x2 else y] *)

Theorem Example11_M:   (If  (Mvar 1)#? (Mvar 2) then (Mvar 1) else (Mvar 3)) # (If  (Mvar 1)#?(Mvar 2) then (Mvar 2) else (Mvar 3)).
Proof.
intros.
rewrite EQmsg .
assert(H1: (If (Bvar 0) then (Mvar 1) else (Mvar 3)) #? (If (Bvar 0) then (Mvar 2) else (Mvar 3)) ## (IF (Bvar 0) then ((Mvar 1)#?(If (Bvar 0) then (Mvar 2) else (Mvar 3))) else ((Mvar 3)#?(If (Bvar 0) then (Mvar 2) else (Mvar 3))))).
apply IFMORPH_M3 with (n:=0) (n1:=1)(n2:=2)(n3:=3)  .
apply Forall_ELM_EVAL_B  with (n:=0) (b:= (eqm (Mvar 1) (Mvar 2))) in H1.
simpl in H1.
assert (H2: (IF (Bvar 0) then
    [[4 := If (Bvar 0) then (Mvar 2) else (Mvar 3)]]((Mvar 1)#? (Mvar 4)) else
    [[4 := If (Bvar 0) then (Mvar 2) else (Mvar 3)]]((Mvar 3)#? (Mvar 4))) ##
  (IF (Bvar 0) then [[4 := Mvar 2]](eqm (Mvar 1) (Mvar 4))
   else [[4 := Mvar 3]](eqm (Mvar 3) (Mvar 4))) ).
apply Ex9msg_bol1 with (b:= (Bvar 0))(n1:=2)(n2:=3)(n3:=2)(n4:=3)(n5:=4)(n6:= 4) (b1:= (eqm (Mvar 1) (Mvar 4))) (b2:= (eqm (Mvar 3) (Mvar 4))) .
simpl in H2.
apply Forall_ELM_EVAL_B  with (n:=0) (b:= (eqm (Mvar 1) (Mvar 2))) in H2.
simpl in H2.
rewrite H2 in H1 .
rewrite H1.
assert (H3:   (eqm (Mvar 3) (Mvar 3)) ##   TRue).
apply EQmsg with (x:=(Mvar 3))( y:= (Mvar 3)).
reflexivity. 
rewrite H3.
assert (H4: (IF (Bvar 0) then TRue else FAlse) ## (Bvar 0)).
apply IFTF with (n:=0).
apply Forall_ELM_EVAL_B2 with (n :=0)(b:= (eqm (Mvar 1) (Mvar 2))) in H4.
simpl  in H4.
assert(H6:  (IF (Bvar 0) then (Bvar 0) else TRue) ## (IF (Bvar 0) then TRue else TRue)).
apply IFEVAL_B with (n:=0) (b1:=(Bvar 0)) (b2:= TRue) .
apply Forall_ELM_EVAL_B with (n :=0)(b:= (eqm (Mvar 1) (Mvar 2))) in H6.
simpl  in H6.
rewrite H6.
apply IFSAME_B.
Qed.

Theorem Example11_B:    (IF (eqb  (Bvar 1) (Bvar 2)) then (Bvar 1) else (Bvar 3)) ## ( IF (eqb  (Bvar 1) (Bvar 2)) then (Bvar 2) else (Bvar 3)).
Proof.
intros.
rewrite EQ_Bool .
(assert(H1:  (eqb (IF (Bvar 0) then (Bvar 1) else (Bvar 3)) (IF (Bvar 0) then (Bvar 2) else (Bvar 3))) ## (IF (Bvar 0) then (eqb  (Bvar 1) (IF (Bvar 0) then (Bvar 2) else (Bvar 3))) else (eqb  (Bvar 3) (IF (Bvar 0) then (Bvar 2) else (Bvar 3)))))).
assert (H2 : (eqb (IF (Bvar 0) then (Bvar 1) else (Bvar  3)) (Bvar 4)) ## ( IF (Bvar 0) then (eqb (Bvar 1) (Bvar 4)) else (eqb (Bvar 3) (Bvar 4)))).
apply IFMORPH_B3 with  (n:=0) (n1:=1).
apply Forall_ELM_EVAL_B  with (n:=4) (b:= IF (Bvar 0) then (Bvar 2) else (Bvar 3) )in H2.
simpl in H2.
apply H2.
apply Forall_ELM_EVAL_B  with (n:=0) (b:= (eqb (Bvar 1) (Bvar 2))) in H1.
simpl in H1.
assert (H2:  (IF (Bvar 0) then (eqb (Bvar 1) (IF (Bvar 0) then (Bvar 2) else (Bvar 3))) else (eqb (Bvar 3) (IF (Bvar 0) then (Bvar 2) else (Bvar 3)))) ## (IF (Bvar 0) then (eqb (Bvar 1) (Bvar 2)) else (eqb (Bvar 3) (Bvar 3)))).
apply Ex9bol_bol1 with (n1:=2)(n2:=3)(n3:=2)(n4:=3)(n5:=4)(n6:= 4) (b1:= (eqb (Bvar 1) (Bvar 4))) (b2:= (eqb (Bvar 3) (Bvar 4))) .
apply Forall_ELM_EVAL_B  with (n:=0) (b:= (eqb (Bvar 1) (Bvar 2))) in H2.
simpl in H2.
rewrite H1 .
rewrite H2.
assert (H3:   (eqb (Bvar 3) (Bvar 3)) ## TRue).
apply EQ_Bool with (x:=(Bvar 3))( y:= (Bvar 3)).
reflexivity.
rewrite H3. 
assert (H4: (IF (Bvar 0) then TRue else FAlse) ## (Bvar 0)).
apply IFTF with (n:=0).
apply Forall_ELM_EVAL_B2 with (n :=0)(b:= (eqb (Bvar 1) (Bvar 2))) in H4.
simpl  in H4.
assert(H6: (IF (Bvar 0) then (Bvar 0) else TRue) ## ( IF (Bvar 0) then TRue else TRue)).
apply IFEVAL_B with (n:=0) (b1:=(Bvar 0)) (b2:= TRue) .
apply Forall_ELM_EVAL_B with (n :=0)(b:= (eqb (Bvar 1) (Bvar 2))) in H6.
simpl  in H6.
rewrite H6.
apply IFSAME_B.
Qed.

Axiom Example11_B1: forall (n1 n2 n3 :nat), (IF (eqb  (Bvar n1) (Bvar n2)) then (Bvar n1) else (Bvar n3))  ## ( IF (eqb  (Bvar n1) (Bvar n2)) then (Bvar n2) else (Bvar n3)).
Axiom Example11_B2: forall (n1 n2 n3 :nat),  (IF (eqm  (Mvar n1) (Mvar n2)) then (Bvar n1) else (Bvar n3))  ## (IF (eqm  (Mvar n1) (Mvar n2)) then (Bvar n2) else (Bvar n3)).
Axiom Example11_M1:forall(n1 n2 n3:nat),   (If (eqm  (Mvar n1) (Mvar n2)) then (Mvar n1) else (Mvar n3) ) # (If (eqm  (Mvar n1) (Mvar n2)) then (Mvar n2) else (Mvar n3)).
Axiom Example11_M2:forall(n1 n2 n3:nat),   (If (eqb  (Bvar n1) (Bvar n2)) then (Mvar n1) else (Mvar n3) ) # (If (eqb  (Bvar n1) (Bvar n2)) then (Mvar n2) else (Mvar n3)).
