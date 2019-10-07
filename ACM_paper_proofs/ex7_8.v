(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                     Rohit Chadha <chadhar@missouri.edu>              *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)
Load "ex7_7".
(**  This library defines a theorem that states, [if not(b) then x else y = if b then y else x ].
(*<!-- Of course, we use ## (resp. ##) for message (resp. Bool) in lieu of [=]. -->*) *)

Theorem Example16_B :  forall (n:nat) (b1 b2 :Bool), (if_then_else_B (notb  (Bvar n)) b1 b2) ## (if_then_else_B (Bvar n) b2 b1).
Proof.
intros.
unfold notb.
assert(H1: (if_then_else_B (if_then_else_B (Bvar n) FAlse TRue) b1 b2) ##
    (if_then_else_B (Bvar n) (  if_then_else_B FAlse b1 b2) ( if_then_else_B TRue b1 b2))).

apply IFMORPH_B2 .
rewrite H1.
rewrite IFFALSE_B.
rewrite IFTRUE_B.
reflexivity.
Qed.
Theorem Example16_M :  forall (n:nat) (m1 m2:message), (if_then_else_M (notb  (Bvar n)) m1 m2) # (if_then_else_M (Bvar n) m2 m1).
Proof.
intros.
unfold notb.
assert(H1: (if_then_else_M (if_then_else_B (Bvar n) FAlse TRue) m1 m2) #
    (if_then_else_M (Bvar n) (  if_then_else_M FAlse m1 m2) ( if_then_else_M TRue m1 m2))).

apply IFMORPH_M2 .
rewrite H1.
rewrite IFFALSE_M.
rewrite IFTRUE_M.
reflexivity.
Qed.
