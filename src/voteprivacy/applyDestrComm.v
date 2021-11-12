(************************************************************************)
(* Copyright (c) 2017-2018, Ajay Kumar Eeralla <ae266@mail.missouri.edu>*)
(************************************************************************)

Require Export auxDefs.
Require Import Coq.Bool.Bool.
Set Nested Proofs Allowed.
Require Import List.
Import ListNotations.

Section auxProps.
  Axiom ifMorphPair: forall b t1 t2 t3, (t1, If b then t2 else t3) # If b then (t1, t2) else (t1, t3).
  Axiom andB_elim: forall b1 b2 t1 t2, (If b1 & b2 then t1 else t2) # (If b1 then (If b2 then t1 else t2) else t2).
  Axiom ifMorphIfThen: forall b1 b2 t1 t2 t3, (If b1 then (If b2 then t1 else t2) else t3) # (If b2 then (If b1 then t1 else t3) else (If b1 then t2 else t3)).
  Axiom orB_FAlse_r: forall b, b or FAlse = b.
  Axiom orB_FAlse_l: forall b, FAlse or b = b.
  Axiom ifMorphIf: forall b1 b2 b3 b4 t1 t2, (If b1 & (IF b2 then b3 else b4) then t1 else t2) # (If b2 then (If b1 & b3 then t1 else t2) else (If b1 & b4 then t1 else t2)).
  Fixpoint ifMorphDef (f: Mlist -> message) (al: Mlist) (l: Mlist) :=
    match l with
    | nil => f (al ++ nil)
    | cons (If b then t1 else t2) nil  => If b then (f (al ++ (cons t1 nil))) else (f (al ++ (cons t2 nil)))
| h :: tl => match h with
             | If b then t1 else t2 => If b then (ifMorphDef f (al ++ (cons t1 nil)) tl) else (ifMorphDef f (al ++ (cons t2 nil)) tl)
| _ => ifMorphDef f (al ++ (cons h nil)) tl
  end
  end.
  Axiom clos_sub_vtrm: forall n1 s1 n2 s2 t, let mvl:= (distMvars [msg t]) in (cons n1  (cons n2 nil))= mvl \/ (cons n2 (cons n1 nil)) = mvl -> closMsg ({{n1:=s1}} ({{n2:=s2}}t)) = true.

  (* Compute ifMorphDef f nil [O; If FAlse then nonce 1 else O; nonce 2; If TRue then (If TRue then nonce 100 else O) else nonce 4]. *)

  Axiom ifMorphAttComp: forall b f l t, (If b then (f l) else t) # (If b then (ifMorphDef f nil l) else t).
End auxProps.
 Open Scope msg_scope.
(* Section auxTacs. *)
  Ltac rew_ifMorphIf :=
    match goal with
    |[|- context[(If ?B1 & (IF ?B2 then ?B3 else ?B4) then ?T1 else ?T2)] ] => rewrite (@ifMorphIf B1 B2 B3 B4 T1 T2)
    end.
  Ltac apply_ifbr ml1 ml2 b b' x x' y y' := apply (@IFBRANCH_M1 _ ml1 ml2 b b' x x' y y'); simpl.
  Ltac aply_ifbr :=
    match goal with
    | [|- [msg (If ?B1 then ?T1 else ?F1)]
            ~ [msg (If ?B2 then ?T2 else ?F2)] ]
      => apply_ifbr [] [] B1 B2 T1 T2 F1 F2
    | [|- [?X1, msg (If ?B1 then ?T1 else ?F1)]
            ~ [?Y1, msg (If ?B2 then ?T2 else ?F2)] ]
      => apply_ifbr [X1] [Y1] B1 B2 T1 T2 F1 F2
    | [|- [?X1, ?X2, msg (If ?B1 then ?T1 else ?F1)]
            ~ [?Y1, ?Y2, msg (If ?B2 then ?T2 else ?F2)] ]
      => apply_ifbr [X1, X2] [Y1, Y2] B1 B2 T1 T2 F1 F2
    | [|- [?X1, ?X2, ?X3, msg (If ?B1 then ?T1 else ?F1)]
            ~ [?Y1, ?Y2, ?Y3, msg (If ?B2 then ?T2 else ?F2)] ]
      => apply_ifbr [X1, X2, X3] [Y1, Y2, Y3] B1 B2 T1 T2 F1 F2
    | [|- [?X1, ?X2, ?X3, ?X4, msg (If ?B1 then ?T1 else ?F1)]
            ~ [?Y1, ?Y2, ?Y3, ?Y4, msg (If ?B2 then ?T2 else ?F2)] ]
      => apply_ifbr [X1, X2, X3, X4] [Y1, Y2, Y3, Y4] B1 B2 T1 T2 F1 F2
                    (** extend this for other cases *)
    end.

  Proposition freshNeqExt: forall (n: nat) (m: message), ^? m = true /\ (Fresh (cons n nil) [msg m]) = true -> ((nonce n) #? m) ## FAlse.
Proof. intros. pose proof(FRESHNEQ n m).
       apply (@Example10_B ((nonce n)#?m) FAlse FAlse).
       unfold const; auto.
Qed.
Ltac aply_freshneq n :=
  match goal with
  |[|-context[ (nonce n) #? ?X] ] =>  pose proof(@freshNeqExt n X) as tmp; rewrite tmp; try unfold Fresh; try auto
  end.
Axiom compHid: forall (n1 n2: nat) (t1 t2: message) {n} (z: mylist n),
    closMylist [msg t1, msg t2] = true /\ closMylist z = true /\
      Fresh [n1; n2] ([msg t1, msg t2]++z)%msg = true ->
    (|t1|#?|t2|) ## TRue ->
    (z ++ [msg (comm t1 (k n1)), msg (comm t2 (k n2))]) ~ (z ++ [msg (comm t2 (k n1)), msg (comm t1 (k n2))]).

Proposition vchecksImplyVoteEql: (vcheck (v 0)) & (vcheck (v 1)) ## TRue -> (|v 0| #? |v 1|) ## TRue.
Proof. intros.
       pose proof(vote_len_eql).
       rewrite H in H0; unfold v in H0; red_in H0; try auto.
Qed.
Ltac aplyCompHid :=
  match goal with
  | [|- [msg (comm ?V0 (kc (nonce ?N2))), msg (comm ?V1 (kc (nonce ?N3)))]
          ~ [msg (comm _ (kc (nonce _))), msg (comm _ (kc (nonce _)))] ]
    => apply (@compHid N2 N3 V0 V1 _ []%msg); try apply vchecksImplyVoteEql; try auto; try assumption
  end.

(* End auxTacs. *)
(* Definition V (b:bool) := *)
(*     match b with *)
(*     | false => (V0 (nonce 0)) *)
(*     | true => (V1 (nonce 0)) *)
(*     end. *)

(*   Definition cn (b:bool) :nat := *)
(*     match b with *)
(*     | false => 0 *)
(*     | true => 1 *)
(*     end. *)
(* SearchAbout eqb%bool. *)
(** abbreviations *)

Definition sr n := rs (nonce n).
Definition t0 seed1 seed2 := (((vk 0), (Mvar 0), sign (Mvar 0) (ssk 0) (sr seed1)), ((vk 1), (Mvar 1), sign (Mvar 1) (ssk 1) (sr seed2))).

Definition tau n (m:message) := match n, m with
                                | 1, m => (pi1 m)
                                | 2, m => (pi1 (pi2 m))
                                | 3, m => (pi2 (pi2 m))
                                | _, _ => O
                                end.

Definition d n x := (dec (tau n x) (ske 11)).
Definition pvchecks x := ((pi2 (d 1 x)) #? TWO) & ((pi2 (d 2 x)) #? TWO) & ((pi2 (d 3 x)) #? TWO).
Definition pochecks x := ((tau 3 (d 1 x)) #? THREE) & ((tau 3 (d 2 x)) #? THREE) & ((tau 3 (d 3 x)) #? THREE).

Definition dist x := !((d 1 x) #? (d 2 x)) & !((d 1 x) #? (d 3 x))& ! ((d 2 x) #? (d 3 x)).
Definition isin (x y:message):Bool := (x #? (tau 1 y)) or (x #? (tau 2 y)) or (x #? (tau 3 y)).
Definition bcheck (x y:message):Bool := (isin x ((tau 1 (pi2 (tau 1 y))), ((tau 1 (pi2 (tau 2 y))), (tau 1 (pi2 (tau 3 y)))))).
Definition ncheck (x y:message):Bool := (isin x ((tau 3 (pi2 (tau 1 y))), ((tau 3 (pi2 (tau 2 y))), (tau 3 (pi2 (tau 3 y)))))).


                            Definition lbl:= |(nonce 100)|.
Definition label x y := If (x #? (tau 2 (pi2 (tau 1 y)))) then (pi1 (tau 1 y))
                           else  (If (x#? (tau 2 (pi2 (tau 2 y)))) then (pi1 (tau 2 y))
                                                       else (If (x #? (tau 2 (pi2 (tau 3 y)))) then (pi1 (tau 3 y))
                                                             else O)).

Definition bnlcheck( x y z:message):Bool:= (bcheck x z) & (|(label x z)| #? lbl) & (ncheck y z).

Definition mvchecks x (n n':nat) := (dist (x n n')) & (pvchecks (x n n')).

Definition p n x := ( (tau 1 (d n x)), (tau 2 (d n x))).

Definition sotrm x := (shufl (p 1 x) (p 2 x) (p 3 x)).

Definition isink (x y:message):Bool := (x #? (tau 2 (d 1 y))) or (x #? (tau 2 (d 2 y))) or (x #? (tau 2 (d 3 y))).

Lemma tau1: forall x y z, (tau 1 (x, (y, z))) # x.
Proof. intros. unfold tau. rewrite proj1; auto. reflexivity.
Qed.
Lemma tau2: forall x y z, (tau 2 (x, (y, z))) # y.
Proof. intros. unfold tau; rewrite proj2, proj1;auto. reflexivity. Qed.
Lemma tau3: forall x y z, (tau 3 (x, (y, z))) # z.
Proof. intros. unfold tau. repeat rewrite proj2; try reflexivity.
Qed.
(* better to apply nodup seperately *)
Axiom nodup: forall {m} (l1 l2: mylist m), let l1' := conv_mylist_listos l1 in
                                           let l2' := conv_mylist_listos l2 in
                                           let l1'' := noDup l1' in
                                           let l2'' := noDup l2' in
                                           let y:= oslToMylist l1'' l2'' in
                                           (pi1ProdMylist y) ~ (pi2ProdMylist y) -> l1 ~ l2.


Proposition destrComm:
      let v0 := V0 (f (toListm phi0)) in
      let v1 := V1 (f (toListm phi0)) in
      (* (| v0 |) #? (| v1 |) ## TRue -> *)
      (vcheck v0) & (vcheck v1) ## TRue ->
      (* Fresh [1; 2; 3; 4] [msg t, msg v0, msg v1, msg t0, msg t1] = true -> *)
      (* closMylist [msg t] = true -> *)
      (* (Datatypes.length (distMvars [msg t0, msg t1]) =? 2)%nat = true -> *)
      (* bVarMylist [msg t0, msg t1] = nil -> *)
      (* let mvl := [5; 6] in *)
      (* mVarMsg t0 = mvl /\ mVarMsg t1 = mvl -> *)
      (* Bothsides *)
      let r0 := (r 1) in
      let r1 := (r 2) in
      let k0 := (kc (nonce 3)) in
      let k1 := (kc (nonce 4)) in
      (* Left-side *)
      let c00 := (comm v0 k0) in
      let c11 := (comm v1 k1) in
      let t := pubkey (f (toListm phi0)) in
      let b00 := (bl c00 t r0) in
      let b11 := (bl c11 t r1) in
      let t0 := (((vk 0), (Mvar 5), sign (Mvar 5) (ssk 0) (sr 14)), ((vk 1), (Mvar 6), sign (Mvar 6) (ssk 1) (sr 15))) in
      let t1 := (t0, f (cons t0 nil)) in
      let t2 := ({{ 5 := (bl c00 t r0) }} ({{ 6:=(bl c11 t r1) }} t0)) in
      let t3 := ({{ 5 := (bl c00 t r0) }} ({{ 6:=(bl c11 t r1) }} t1)) in
      let acc00 := (acc c00 t r0 t2) in
      let acc11 := (acc c11 t r1 t3) in
      let e00 := (enc ((c00, ((ub c00 t r0 t2), (nonce 20))), TWO) (pke 11) (er 7)) in
      let e11 := (enc ((c11, ((ub c11 t r1 t3), (nonce 21))), TWO) (pke 11) (er 8)) in
      let phi02:= [msg b00, msg b11, msg e00, msg e11] in
      let fphi02:= f (toListm phi02) in
      let pv00 := (c00, ((ub c00 t r0 t2), (nonce 20))) in
      let pv11 := (c11, ((ub c11 t r1 t3), (nonce 21))) in
      let s0 := (If (! (isin pv00 ((pi1 (d 1 fphi02)), ((pi1 (d 2 fphi02)), (pi1 (d 3 fphi02)))))) then (shufl (pi1 (d 1 fphi02)) (pi1 (d 2 fphi02)) (pi1 (d 3 fphi02))) else O)in
      let dv0 := (If (dist fphi02) & (pvchecks fphi02) then s0 else |_) in
      let phi03:= (phi02 ++[msg dv0])%msg in
      let fphi03 := f (toListm phi03) in
      let l00 := (If (bnlcheck c00 (nonce 20) fphi03) then (enc ((label c00 fphi03), (k0, THREE)) (pke 11) (er 9)) else O) in
      let l11 := (If (bnlcheck c11 (nonce 21) fphi03) then (enc ((label c11 fphi03), (k1, THREE)) (pke 11) (er 10)) else O) in
      let phi05:= (phi03++[msg l00, msg l11])%msg in
      let fphi05 := f (toListm phi05) in
      let do0 := (If (dist fphi05) & (pochecks fphi05) & (((isink k0 fphi05) & (isink k1 fphi05))) (* or (! ((isink k0 fphi05)or (isink k1 fphi05))))*) then (sotrm fphi05) else |_) in
      (* let t0s0 := (If acc00 & acc11 then ((e00, (e11, dv0)), (l00, (l11, do0))) else |_) in *)
      let t0s0 := (If acc00 & acc11 then (e00, e11) else |_) in

      (* Right-side *)
      let c10 := (comm v1 k0) in
      let c01 := (comm v0 k1) in
      let b10 := (bl c10 t r0) in
      let b01 := (bl c01 t r1) in
      let t4 := ({{ 5 := (bl c10 t r0) }} ({{ 6:=(bl c01 t r1) }} t0)) in
      let t5 := ({{ 5 := (bl c10 t r0) }} ({{ 6:=(bl c01 t r1) }} t1)) in
      let acc10 := (acc c10 t r0 t4) in
      let acc01 := (acc c01 t r1 t5) in
      let e10 := (enc ((c10, ((ub c10 t r0 t4), (nonce 20))), TWO) (pke 11) (er 7)) in
      let e01 := (enc ((c01, ((ub c01 t r1 t5), (nonce 21))), TWO) (pke 11) (er 8)) in
      let pv10 := (c10, ((ub c10 t r0 t4), (nonce 20))) in
      let pv01 := (c01, ((ub c01 t r1 t5), (nonce 21))) in
      let phi12:= [msg b10, msg b01, msg e10, msg e01] in
      let fphi12:= f (toListm phi12) in
      let s1 := (If (! (isin pv10 ((pi1 (d 1 fphi12)), ((pi1 (d 2 fphi12)), (pi1 (d 3 fphi12)))))) then (shufl (pi1 (d 1 fphi12)) (pi1 (d 2 fphi12)) (pi1 (d 3 fphi12))) else O)in
      let dv1 := (If (dist fphi12) & (pvchecks fphi12) then s1 else |_) in
      let phi13:= (phi12 ++[msg dv1])%msg in
      let fphi13 := f (toListm phi13) in
      let l10 := (If (bnlcheck c10 (nonce 20) fphi13) then (enc ((label c10 fphi13), (k0, THREE)) (pke 11) (er 9)) else O) in
      let l01 := (If (bnlcheck c01 (nonce 21) fphi13) then (enc ((label c01 fphi13), (k1, THREE)) (pke 11) (er 10)) else O) in
      let phi15:= (phi13++[msg l10, msg l01])%msg in
      let fphi15 := f (toListm phi15) in
      let do1 := (If (dist fphi15)& (pochecks fphi15)& (((isink k0 fphi15)&(isink k1 fphi15)))(* or (! ((isink k0 fphi15)or (isink k1 fphi15))))*) then (sotrm fphi15) else |_) in
      (* let t1s1 := (If acc10 & acc01 then ((e10, (e01, dv1)), (l10, (l01, do1))) else |_) in *)
      let t1s1 := (If acc10 & acc01 then (e10, e01) else |_) in
      (* (occur_name_mylist 100 [msg t, msg t0, msg t1] = false) -> *)
      (* (Fresh (cons 0 nil) [msg t, msg t2, msg t3, msg t4, msg t5] = true) -> *)
      [msg b00, msg b11, msg t0s0] ~ [msg b10, msg b01, msg t1s1].
Proof. intros; aplyDestrComm.
       apply nodup.
       simpl. unfold c10, k0.
       aplyCompHid.
       Qed.

