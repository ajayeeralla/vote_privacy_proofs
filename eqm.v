Require Export ex71.
(** This library a defines a theorem that states, [x = y <-> EQ(x, y) = true] *)

(*Axiom test: forall  (x:Bool) (P:Bool -> Prop),
       P x -> forall y : Bool, x ## y -> P y.*)
Axiom test: forall (b1 b2:Bool){n:nat}(t: Bool->mylist n), b1  ## b2 -> (t  b1) ~ (t  b2).
Theorem EQ_Bool: forall(x y:Bool),   x ## y <->   (eqb x y) ## (TRue) .
Proof.
split.
intros.
apply Example10_B with (F:= TRue) (z:= FAlse) in H.
unfold const in H.
apply H.
intros.
assert(H1: [bol (eqb x y)] ~ [bol TRue]).
apply test with (b1:=eqb x y) (b2:=TRue) (t:= fun x => [bol x]).
apply H.
apply H1.
Qed.

Theorem EQmsg : forall(x y:message),  x # y <->  (eqm x y) ## TRue .
Proof.
split.
intros.
apply Example10_B  with (F:= TRue)(z:= FAlse)in H.
unfold const in H.
apply H.
intros.
assert(H1: [bol (eqm x y)] ~[bol TRue]).
apply test with (b1 := eqm x y) (b2:= TRue) (t:= fun x => [bol x]).
apply H.
apply H1.
Qed.

