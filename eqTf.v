(************************************************************************)
(* Copyright (c) 2015-2019, Ajay Kumar Eeralla                          *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(************************************************************************)    

Require Export eqbranch.

(** This library defines a theorem, [(eqb TRue FAlse)] = FAlse *)

Theorem Ex13bol:  (eqb  TRue FAlse) ##  FAlse.
Proof.
assert(H : (Bvar 1) ##  (IF (Bvar 1) then TRue else FAlse) ) .
rewrite IFTF with (n :=1) . reflexivity.
apply Forall_ELM_EVAL_B with (n:=1)(b:= (eqb  TRue FAlse)) in H .
simpl in H.
assert(H1 : (IF (eqb  (Bvar 1)  (Bvar 2)) then [3 := (Bvar 1)](Bvar 3) else FAlse) ## (IF (eqb (Bvar 1)(Bvar 2)) then [3 := (Bvar 2)](Bvar 3) else FAlse)).
rewrite eqbrbol_bol with (n1:= 1) (n2:= 2)(b2:=FAlse)(b1:=(Bvar 3)).
reflexivity.
simpl in H1.
apply Forall_ELM_EVAL_B with (n:=1)(b:= TRue) in H1 .
simpl in H1.
apply Forall_ELM_EVAL_B with (n:=2)(b:= FAlse) in H1 .
simpl in H1.
rewrite H1 in H.
rewrite IFSAME_B in H. apply H.
Qed.
