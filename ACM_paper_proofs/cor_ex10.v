(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                     Rohit Chadha <chadhar@missouri.edu>              *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)
Load "ex10".

(** This library a defines a theorem that states, [x = y <-> EQ(x, y) = true] *)

(*Axiom test: forall  (x:Bool) (P:Bool -> Prop),
       P x -> forall y : Bool, x ## y -> P y.*)
Axiom test: forall (b1 b2:Bool){n:nat}(t: Bool->mylist n), b1  ## b2 -> (t  b1) ~ (t  b2).
Theorem EQ_Bool: forall(x y:Bool),   x ## y <->   (EQ_B  x y) ## (TRue) .
Proof.
split.
intros.
apply Example10_B with (F:= TRue) (z:= FAlse) in H.
unfold const in H.
apply H.
intros.
assert(H1: [bol (EQ_B x y)] ~ [bol TRue]).
apply test with (b1:=EQ_B x y) (b2:=TRue) (t:= fun x => [bol x]).
apply H.
apply H1.
Qed.

Theorem EQmsg : forall(x y:message),  x # y <->  (EQ_M x y) ## TRue .
Proof.
split.
intros.
apply Example10_B  with (F:= TRue)(z:= FAlse)in H.
unfold const in H.
apply H.
intros.
assert(H1: [bol (EQ_M x y)] ~[bol TRue]).
apply test with (b1 := EQ_M x y) (b2:= TRue) (t:= fun x => [bol x]).
apply H.
apply H1.
Qed.

