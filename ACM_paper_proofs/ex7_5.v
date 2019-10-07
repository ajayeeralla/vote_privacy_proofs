
(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                     Rohit Chadha <chadhar@missouri.edu>              *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)
Load "eqbranch".

(** This library defines a theorem, [(EQ_B TRue FAlse)] = FAlse *)

Theorem Ex13bol:  (EQ_B  TRue FAlse) ##  FAlse.
Proof.
assert(H : (Bvar 1) ##  (if_then_else_B (Bvar 1) TRue FAlse) ) .
rewrite IFTF with (n :=1) . reflexivity.
apply Forall_ELM_EVAL_B with (n:=1)(b:= (EQ_B  TRue FAlse)) in H .
simpl in H.
assert(H1 : (if_then_else_B (EQ_B  (Bvar 1)  (Bvar 2))[3 := (Bvar 1)](Bvar 3) FAlse) ## (if_then_else_B (EQ_B  (Bvar 1)(Bvar 2)) [3 := (Bvar 2)](Bvar 3)  FAlse)).
rewrite EQ_BRbol_bol with (n1:= 1) (n2:= 2)(b2:=FAlse)(b1:=(Bvar 3)).
reflexivity.
simpl in H1.
apply Forall_ELM_EVAL_B with (n:=1)(b:= TRue) in H1 .
simpl in H1.
apply Forall_ELM_EVAL_B with (n:=2)(b:= FAlse) in H1 .
simpl in H1.
rewrite H1 in H.
rewrite IFSAME_B in H. apply H.
Qed.
