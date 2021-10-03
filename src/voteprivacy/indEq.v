(************************************************************************)
(* Copyright (c) 2015-2019, Ajay Kumar Eeralla                          *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(************************************************************************)    

Require Export ifMorph.

(** This library defines a theorem that states,[ [[ msg x]] ~ [[ msg y]] -> x # y.] *)
 
Theorem Example10_M: forall (x  F z : message), [msg x] ~ [msg (const F z )] -> x # (const F z) .
 Proof. 
intros.
simpl in H.
unfold const in H.
unfold const.
apply FUNCApp_const with (a := [msg F])(ml1 := ([msg x]))(ml2 := [msg F]) in H.
unfold const in H. unfold appMylist in H.
simpl in H. 

apply FUNCApp_eqm with (p1 := 2) (p2:=1) in H. 
simpl in H.
unfold eqm_at_pos in H.
unfold chkmsg_os in H. unfold getelt_at_pos in H.
simpl in H.
apply RESTR_proj with (p:=3) in H. unfold proj_at_pos in H. simpl in H.
apply RESTR_proj with (p:=2) in H. unfold proj_at_pos in H. simpl in H.
assert (J:[bol (eqm F F) ] ~[bol TRue]) .
assert(K: (EQm F F)).
reflexivity.
apply K.
assert (K:[bol (eqm x F)] ~[bol TRue]) .
apply EQI_trans with (ml2 := [bol (eqm F F)]).
assumption. assumption. assumption.
Qed.

(** The following theorem states that [x~f -> x=f] *)

Theorem Example10_B: forall (x  F z : Bool), [bol x] ~ [bol (const F z )] ->  x ## (const F  z) .
 Proof.
intros.
simpl in H.
unfold const in H.
unfold const.
apply FUNCApp_const with (a := [bol F])(ml1 := ([bol x]))(ml2 := [bol F]) in H.
unfold const in H.
simpl in H.
pose proof (FUNCApp_eqb).
apply FUNCApp_eqb with ( p1:=2)(p2:=1) in H.
unfold appMylist in H.
unfold eqb_at_pos in H.
simpl in H.
assert (J:[bol (eqb F F) ] ~[bol TRue]) .
assert(K: (EQb F F)).
reflexivity.
apply K.
assert (K:[bol (eqb x F)] ~[bol TRue]) .
apply EQI_trans with (ml2 := [bol (eqb F F)]).
apply H.
apply J.
apply K.
Qed.
