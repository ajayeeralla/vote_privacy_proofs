(************************************************************************) 
(* Copyright (c) 2017-2018, Ajay Kumar Eeralla <ae266@mail.missouri.edu>*)
(************************************************************************) 
Require Export destructTerm.
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

(* Section auxTacs. *)
  Ltac rew_ifMorphIf :=
    match goal with
    |[|- context[(If ?B1 & (IF ?B2 then ?B3 else ?B4) then ?T1 else ?T2)] ] => rewrite (@ifMorphIf B1 B2 B3 B4 T1 T2)
    end.
  Ltac apply_ifbr ml1 ml2 b b' x x' y y' := apply (@IFBRANCH_M1 _ ml1 ml2 b b' x x' y y'); simpl.
  Ltac aply_ifbr :=
    match goal with
    | [|- (Cons _ _ (msg (If ?B1 then ?T1 else ?F1)) (Nil _))
            ~ (Cons _ _ (msg (If ?B2 then ?T2 else ?F2)) (Nil _))]
        => apply_ifbr [] [] B1 B2 T1 T2 F1 F2
    | [|- (Cons _ _ ?X4 (Cons _ _ (msg (If ?B1 then ?T1 else ?F1)) (Nil _)))
            ~ (Cons _ _ ?Y4 (Cons _ _ (msg (If ?B2 then ?T2 else ?F2)) (Nil _)))]
      => apply_ifbr [X4] [Y4] B1 B2 T1 T2 F1 F2
    | [|- (Cons _ _ ?X3 (Cons _ _ ?X4 (Cons _ _ (msg (If ?B1 then ?T1 else ?F1)) (Nil _))))
            ~ (Cons _ _ ?Y3 (Cons _ _ ?Y4 (Cons _ _ (msg (If ?B2 then ?T2 else ?F2)) (Nil _))))]
      => apply_ifbr [X3, X4] [Y3, Y4] B1 B2 T1 T2 F1 F2
    |[|- (Cons _ _ ?X2 (Cons _ _ ?X3 (Cons _ _ ?X4 (Cons _ _ (msg (If ?B1 then ?T1 else ?F1)) (Nil _)))))
           ~ (Cons _ _ ?Y2 (Cons _ _ ?Y3 (Cons _ _ ?Y4 (Cons _ _ (msg (If ?B2 then ?T2 else ?F2)) (Nil _)))))]
     => apply_ifbr [X2, X3, X4] [Y2, Y3, Y4] B1 B2 T1 T2 F1 F2
    | [|- (Cons _ _ ?X1 (Cons _ _ ?X2 (Cons _ _ ?X3 (Cons _ _ ?X4 (Cons _ _ (msg (If ?B1 then ?T1 else ?F1)) (Nil _))))))
            ~ (Cons _ _ ?Y1 (Cons _ _ ?Y2 (Cons _ _ ?Y3 (Cons _ _ ?Y4 (Cons _ _ (msg (If ?B2 then ?T2 else ?F2)) (Nil _))))))]
      => apply_ifbr [X1, X2, X3, X4] [Y1, Y2, Y3, Y4] B1 B2 T1 T2 F1 F2
                    (** extend this for other cases *)
    end.
(* End auxTacs. *)

Compute er.
Module aux.
  Export destructTerm.
  Fixpoint submsg_bol pk r (t': message)(s: message) (b: Bool): Bool :=
    match b with
    | eqb  b1 b2 =>  (eqb (submsg_bol pk r t' s b1) (submsg_bol pk r t' s b2))
    | eqm t1 t2 => (eqm (submsg_msg pk r t' s t1) (submsg_msg pk r t' s t2))
    | ifb_then_else_ t1 t2 t3 => (IF (submsg_bol pk r t' s t1) then (submsg_bol pk r t' s t2) else (submsg_bol pk r t' s t3))
    | ver t1 t2 t3 => ver (submsg_msg pk r t' s t1) (submsg_msg pk r t' s t2) (submsg_msg pk r t' s t3)
    | bver t1 t2 t3 => bver (submsg_msg pk r t' s t1) (submsg_msg pk r t' s t2) (submsg_msg pk r t' s t3)
    | acc t1 t2 t3 t4 => acc (submsg_msg pk r t' s t1) (submsg_msg pk r t' s t2) (submsg_msg pk r t' s t3) (submsg_msg pk r t' s t4)
    | _ => b
    end
  with submsg_msg pk r (t': message)(s: message) (t: message): message :=
         match t with
         | enc t1 t2 t3 => match t2, t3 with
                           | pi1 (ke (nonce n1)), re (nonce n2) => if ((n1 =? pk)%nat && (n2 =? r)%nat)&& message_beq t1 t'
                                                                   then enc s t2 t3 else t
                           | _, _ => t
                           end
         | _ => t
                  
         end.

  Fixpoint submsg_os pk r (t': message) (s: message) (os: oursum): oursum :=
    match os with
    | msg t => msg (submsg_msg pk r t' s t)
    | bol b => bol (submsg_bol pk r t' s b)
    end.

  Fixpoint submsgMylist pk r (t': message) (s: message) {n} (ml: mylist n): mylist n :=
    match ml with
    | [] => []
    | h:t => (submsg_os pk r t' s h): submsgMylist pk r t' s t
    end.

  (* Replace nonce directly as the above definition seems slow  *)
  Fixpoint repNonceBol n n' b: Bool :=
  match b with
    | eqb  b1 b2 =>  (eqb (repNonceBol n n' b1) (repNonceBol n n' b2))
    | eqm t1 t2 => (eqm (repNonceMsg n n' t1) (repNonceMsg n n' t2))
    | ifb_then_else_ t1 t2 t3 => (IF (repNonceBol n n' t1) then (repNonceBol n n' t2) else (repNonceBol n n' t3))
    | ver t1 t2 t3 => ver  (repNonceMsg n n' t1) (repNonceMsg n n' t2) (repNonceMsg n n' t3)
    | bver t1 t2 t3 => bver (repNonceMsg n n' t1) (repNonceMsg n n' t2) (repNonceMsg n n' t3)
    | acc t1 t2 t3 t4 => acc (repNonceMsg n n' t1) (repNonceMsg n n' t2) (repNonceMsg n n' t3) (repNonceMsg n n' t4)
    | _ => b
  end
with repNonceMsg n n' t: message :=
       match t with
         | nonce k => if (k =? n)%nat then (nonce n') else t
         | ifm_then_else_ b1 t1 t2 =>    (If (repNonceBol n n' b1) then (repNonceMsg n n' t1) else (repNonceMsg n n' t2))
         | pair t1 t2 => pair (repNonceMsg n n' t1) (repNonceMsg n n' t2)
         | pi1 t1 =>  pi1 (repNonceMsg n n' t1)
         | pi2 t1 =>  pi2 (repNonceMsg n n' t1)
         | L t1 =>  L (repNonceMsg n n' t1)
         | to t1 => to  (repNonceMsg n n' t1)
         | f l =>  (f (@map message message  (repNonceMsg n n') l))
         (** foo function symbol *)
         (** FOO syntax *)
         (** Vote values *)
         | V0 t1 => V0 (repNonceMsg n n' t1)
         | V1 t1 => V1 (repNonceMsg n n' t1)
         (** Public Key *)
         | pubkey t1 => pubkey (repNonceMsg n n' t1)
         (** Commitments *)
         | kc t1 => kc (repNonceMsg n n' t1)
         | comm t1 t2 => comm (repNonceMsg n n' t1) (repNonceMsg n n' t2)
         | open t1 t2 t3 => open (repNonceMsg n n' t1) (repNonceMsg n n' t2) (repNonceMsg n n' t3)
         (** Shuffling *)
         | shufl t1 t2 t3 =>  shufl (repNonceMsg n n' t1) (repNonceMsg n n' t2) (repNonceMsg n n' t3)
         (** Encryptions *)
         | ke t1 => ke (repNonceMsg n n' t1)
         | re t1 => re (repNonceMsg n n' t1)
         | enc t1 t2 t3 =>  enc (repNonceMsg n n' t1) (repNonceMsg n n' t2) (repNonceMsg n n' t3)
         | dec t1 t2 =>  dec (repNonceMsg n n' t1) (repNonceMsg n n' t2)
           (** Blind Signatures *)
         | kb t1 => kb (repNonceMsg n n' t1)
         | rb t1 => rb (repNonceMsg n n' t1)
         | bsign t1 t2 t3 =>  bsign (repNonceMsg n n' t1) (repNonceMsg n n' t2) (repNonceMsg n n' t3)
         | bl t1 t2 t3 =>  bl (repNonceMsg n n' t1) (repNonceMsg n n' t2) (repNonceMsg n n' t3)
         | ub t1 t2 t3 t4 => ub (repNonceMsg n n' t1) (repNonceMsg n n' t2)  (repNonceMsg n n' t3)   (repNonceMsg n n' t4)
         (** Signatures *)
         | ks t1 => ks (repNonceMsg n n' t1)
         | rs t1 => rs (repNonceMsg n n' t1)
         | sign t1 t2 t3 => sign (repNonceMsg n n' t1) (repNonceMsg n n' t2) (repNonceMsg n n' t3)
         (* | z t1 => z t1 *)
         | compl t1 => compl (repNonceMsg n n' t1)
         (** all other constrs *)
         | _ => t
       end.

  Fixpoint repNonceOs n n' os: oursum :=
    match os with
    | msg t => msg (repNonceMsg n n' t)
    | bol b => bol (repNonceBol n n' b)
    end.
  
  Fixpoint repNonceMylist n n' {m} (l: mylist m): mylist m :=
    match l with
    | [] => []
    | h:t => (repNonceOs n n' h) : (repNonceMylist n n' t)
    end.
End aux.

Section lemma_25.

  Definition V (b:bool) :=
    match b with
    | false => (V0 (nonce 0))
    | true => (V1 (nonce 0))
    end.

  Definition cn (b:bool) :nat :=
    match b with
    | false => 0
    | true => 1
    end.
(* SearchAbout eqb%bool. *)
(** abbreviations *)

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

  Open Scope msg_scope.
  
  (** **)
Axiom funcapp_f1m': forall {n n'} f p1 (z z':mylist n) (z1 z1':mylist n'), (z ++ z1) ~ (z' ++ z1') -> ((z ++ z1) ++ [msg (f (ostomsg (getelt_at_pos p1 z1)))]) ~ ((z' ++ z1') ++ [msg (f (ostomsg (getelt_at_pos p1 z1')))]).
Ltac funcapp_f1m'_in g n H:= apply funcapp_f1m' with (f:=g) (p1:=n) in H; unfold getelt_at_pos in H; simpl in H.
Axiom ifmor_ifm: forall f b x y, (f (If b then x else y)) # (If b then (f x) else (f y)).

Lemma extFuncapp1: forall n b b' x x' y y' (z z': mylist n) g, (z ++ [bol b, msg (If b then x else y)]) ~ (z' ++ [bol b', msg (If b' then x' else y')]) -> (z ++ [bol b, msg (If b then x else y), msg (If b then (g x) else |_)])~ (z' ++ [bol b', msg (If b' then x' else y'), msg (If b' then (g x') else |_)]).
Proof. intros.
       funcapp_f1m'_in g 2 H.
       simpl.
       repeat rewrite ifmor_ifm in H.
       funcapp_fm_last |_ H; auto. apply ind_assoc in H; simpl in H.
       apply funcapp_f3bm' with (f:= (ifm_then_else_)) (p1:= 1) (p2:=3) (p3:=4) in H; unfold getelt_at_pos; simpl in H.
       simpl in H.
       (********************)
       apply ind_assoc in H; simpl in H.
       do 2  apply restr with (p:= droplastsec) in H; unfold droplastsec in H; simpl in H; simpl; try rewrite Nat.eqb_refl; auto.
       repeat rewrite aply_ifeval_gen in H;auto. Qed.

Axiom eqm_cong: forall m1 m2 m3 m4, m1 # m2 -> m3 # m4 -> (eqm m1 m3) ## (eqm m2 m4).
Add Parametric Morphism: (@ eqm) with
    signature EQm ==> EQm ==> EQb as eqm_mor.
Proof. intros. rewrite H, H0. reflexivity. Qed.

Axiom orB_cong: forall b1 b2 b3 b4, b1 ## b2 -> b3 ## b4 -> (IF b1 then TRue else b3) ## (IF b2 then TRue else b4).
Add Parametric Morphism: (@orB) with
      signature EQb ==> EQb ==> EQb as orB_mor.
Proof. intros. apply orB_cong; auto. Qed.
Import aux.
(* Require Import Coq.Lists.List. *)
Lemma rep_first_ballot: forall t t0 t1 : message,
      let v0 := V0 (nonce 0) in
      let v1 := V1 (nonce 0) in
      (| v0 |) #? (| v1 |) ## TRue ->
      Fresh [1; 2; 3; 4] [msg t, msg v0, msg v1, msg t0, msg t1] = true ->
      closMylist [msg t] = true ->
      (Datatypes.length (distMvars [msg t0, msg t1]) =? 2)%nat = true ->
      bVarMylist [msg t0, msg t1] = nil ->
      let mvl := [5; 6] in
      mVarMsg t0 = mvl /\ mVarMsg t1 = mvl ->
      (* Bothsides *)
      let r0 := (r 1) in
      let r1 := (r 2) in
      let k0 := (kc (nonce 3)) in
      let k1 := (kc (nonce 4)) in
      (* Left-side *)
      let c00 := (comm v0 k0) in
      let c11 := (comm v1 k1) in
      let b00 := (bl c00 t r0) in
      let b11 := (bl c11 t r1) in
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
      let phi03:= phi02 ++[msg dv0] in
      let fphi03 := f (toListm phi03) in
      let l00 := (If (bnlcheck c00 (nonce 20) fphi03) then (enc ((label c00 fphi03), (k0, THREE)) (pke 11) (er 9)) else O) in
      let l11 := (If (bnlcheck c11 (nonce 21) fphi03) then (enc ((label c11 fphi03), (k1, THREE)) (pke 11) (er 10)) else O) in
      let phi05:= phi03++[msg l00, msg l11] in
      let fphi05 := f (toListm phi05) in
      let do0 := (If (dist fphi05) & (pochecks fphi05) & (((isink k0 fphi05) & (isink k1 fphi05))) (* or (! ((isink k0 fphi05)or (isink k1 fphi05))))*) then (sotrm fphi05) else |_) in
      let t0s0 := (If acc00 & acc11 then ((e00, (e11, dv0)), (l00, (l11, do0))) else |_) in

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
      let phi13:= phi12 ++[msg dv1] in
      let fphi13 := f (toListm phi13) in
      let l10 := (If (bnlcheck c10 (nonce 20) fphi13) then (enc ((label c10 fphi13), (k0, THREE)) (pke 11) (er 9)) else O) in
      let l01 := (If (bnlcheck c01 (nonce 21) fphi13) then (enc ((label c01 fphi13), (k1, THREE)) (pke 11) (er 10)) else O) in
      let phi15:= phi13++[msg l10, msg l01] in
      let fphi15 := f (toListm phi15) in
      let do1 := (If (dist fphi15)& (pochecks fphi15)& (((isink k0 fphi15)&(isink k1 fphi15)))(* or (! ((isink k0 fphi15)or (isink k1 fphi15))))*) then (sotrm fphi15) else |_) in
      let t1s1 := (If acc10 & acc01 then ((e10, (e01, dv1)), (l10, (l01, do1))) else |_) in
      (occur_name_mylist 100 [msg t, msg t0, msg t1] = false) ->
      (Fresh (cons 0 nil) [msg t, msg t2, msg t3, msg t4, msg t5] = true) ->
      [msg b00, msg b11, msg t0s0] ~ [msg b10, msg b01, msg t1s1].

 (* Proof.  intros. *)
 (*        unfold t0s0, t1s1. *)
       
 (*        (* Replace nonce 20 with nonce 50 in the first ballot *)
        (* Left side *) *)
 (*        (* To prove left frame indistinguishable to the following using CCA2 *) *)
 (*        pose (L':= let e00':= (enc ((c00, ((ub c00 t r0 t2), (nonce 50))), TWO) (pke 11) (er 7)) in *)
 (*                   let phi02':= [msg b00, msg b11, msg e00', msg e11] in *)
 (*                   let fphi02':= f (toListm phi02') in *)
 (*                   (* let pv00 := (c00, ((ub c00 t r0 t2), (nonce 20))) in *) *)
 (*                   (* let pv11 := (c11, ((ub c11 t r1 t3), (nonce 21))) in *) *)
 (*                   let s0' := (If (! (isin pv00 ((pi1 (d 1 fphi02')), ((pi1 (d 2 fphi02')), (pi1 (d 3 fphi02')))))) then (shufl (pi1 (d 1 fphi02')) (pi1 (d 2 fphi02')) (pi1 (d 3 fphi02'))) else O)in *)
 (*                   let dv0' := (If (dist fphi02') & (pvchecks fphi02') then s0' else |_) in *)
 (*                   let phi03':= phi02' ++[msg dv0'] in *)
 (*                   let fphi03' := f (toListm phi03') in *)
 (*                   let l00' := (If (bnlcheck c00 (nonce 20) fphi03') then (enc ((label c00 fphi03'), (k0, THREE)) (pke 11) (er 9)) else O) in *)
 (*                   let l11' := (If (bnlcheck c11 (nonce 21) fphi03') then (enc ((label c11 fphi03'), (k1, THREE)) (pke 11) (er 10)) else O) in *)
 (*                   let phi05':= phi03'++[msg l00', msg l11'] in *)
 (*                   let fphi05' := f (toListm phi05') in *)
 (*                   let do0' := (If (dist fphi05') & (pochecks fphi05') & (((isink k0 fphi05') & (isink k1 fphi05')) or (! ((isink k0 fphi05')or (isink k1 fphi05')))) then (sotrm fphi05') else |_) in *)
 (*                   let t0s0' := (If acc00 & acc11 then ((e00', (e11, dv0')), (l00', (l11', do0'))) else |_) in *)
 (*                   [msg b00, msg b11, msg t0s0']). *)
 (*        (* To prove right frame indistinguishable to the following using CCA2 *) *)
 (*        pose (R':=  let e10' := (enc ((c10, ((ub c10 t r0 t4), (nonce 50))), TWO) (pke 11) (er 7)) in *)
 (*                    (* let e01 := (enc ((c01, ((ub c01 t r1 t5), (nonce 21))), TWO) (pke 11) (er 8)) in *) *)
 (*                    (* let pv10 := (c10, ((ub c10 t r0 t4), (nonce 20))) in *) *)
 (*                    (* let pv01 := (c01, ((ub c01 t r1 t5), (nonce 21))) in *) *)
 (*                    let phi12':= [msg b10, msg b01, msg e10', msg e01] in *)
 (*                    let fphi12':= f (toListm phi12') in *)
 (*                    let s1' := (If (! (isin pv10 ((pi1 (d 1 fphi12')), ((pi1 (d 2 fphi12')), (pi1 (d 3 fphi12')))))) then (shufl (pi1 (d 1 fphi12')) (pi1 (d 2 fphi12')) (pi1 (d 3 fphi12'))) else O)in *)
 (*                    let dv1' := (If (dist fphi12') & (pvchecks fphi12') then s1' else |_) in *)
 (*                    let phi13':= phi12' ++[msg dv1'] in *)
 (*                    let fphi13' := f (toListm phi13') in *)
 (*                    let l10' := (If (bnlcheck c10 (nonce 20) fphi13') then (enc ((label c10 fphi13'), (k0, THREE)) (pke 11) (er 9)) else O) in *)
 (*                    let l01' := (If (bnlcheck c01 (nonce 21) fphi13') then (enc ((label c01 fphi13'), (k1, THREE)) (pke 11) (er 10)) else O) in *)
 (*                    let phi15':= phi13'++[msg l10', msg l01'] in *)
 (*                    let fphi15' := f (toListm phi15') in *)
 (*                    let do1' := (If (dist fphi15')& (pochecks fphi15')& (((isink k0 fphi15')&(isink k1 fphi15')) or (! ((isink k0 fphi15')or (isink k1 fphi15')))) then (sotrm fphi15') else |_) in *)
 (*                    let t1s1' := (If acc10 & acc01 then ((e10', (e01, dv1)), (l10', (l01', do1'))) else |_) in *)
 (*                    [msg b10, msg b01,  msg t1s1']). *)

        
 (*        Axiom cca2Trans: forall {m} {l1 l2 l1' l2': mylist m}, l1 ~ l1' /\ l2 ~ l2' /\ l1' ~ l2' -> l1 ~ l2. *)
 (*        Ltac aply_cca2Trans L R := *)
 (*          match goal with *)
 (*          | [|- ?X ~ ?Y] => apply (@cca2Trans _ X Y L R) *)
 (*          end. *)
 (*        aply_cca2Trans L' R'. *)
 (*        repeat try split. *)
 (*        (** I will come back and apply cca2 properly here *) *)
 (*        Axiom dummy: forall {n} (l1 l2: mylist n), l1 ~ l2. *)
 (*        apply dummy. apply dummy. *)
 (*        (*** Now we have the goal where the nonce 20 in the first ballot has been replaced with nonce 50 *) *)
 (*        unfold L'. simpl. unfold bnlcheck. *)
 (*        pose proof(FRESHNEQ). *)
 (*        Axiom freshNeqExt: forall (n: nat) (m: message), ^? m = true /\ (Fresh (cons n nil) [msg m]) = true -> ((nonce n) #? m) ## FAlse. *)
 (*        Ltac aply_freshneq n := *)
 (*          match goal with *)
 (*          |[|-context[ (nonce n) #? ?X] ] =>  pose proof(@freshNeqExt n X) as tmp *)
 (*            end. *)
 (*        unfold ncheck. unfold isin.  aply_freshneq 20. *)
 (*        repeat rewrite tmp. *)
 (*        repeat try rewrite andB_FAlse_r, andB_FAlse_l. *)
 (*        redg.    *)
        
 (*          Axiom destrAbstrTerm: forall n t, destrEncMsg n t t = mypair (cons (msg t) nil) (cons (msg t) nil).      *)
 (*           repeat rewrite destrAbstrTerm.  simpl. *)
 (*        Axiom nodup: forall {m} (l1 l2: mylist m), let l1' := conv_mylist_listos l1 in *)
 (*                                           let l2' := conv_mylist_listos l2 in *)
 (*                                           let l1'' := nodupOsl l1' in *)
 (*                                           let l2'' := nodupOsl l2' in *)
 (*                                           let y:= oslToMylist l1'' l2'' in *)
 (*                                           (pi1ProdMylist y) ~ (pi2ProdMylist y) -> l1 ~ l2.                                                   *)
Proof.
        Proposition freshNeqExt: forall (n: nat) (m: message), ^? m = true /\ (Fresh (cons n nil) [msg m]) = true -> ((nonce n) #? m) ## FAlse.
          Proof. intros. pose proof(FRESHNEQ n m).
                 apply (@Example10_B ((nonce n)#?m) FAlse FAlse).
                 unfold const; auto.
          Qed.
        Ltac aply_freshneq n :=
          match goal with
          |[|-context[ (nonce n) #? ?X] ] =>  pose proof(@freshNeqExt n X) as tmp; rewrite tmp; try unfold Fresh; try auto
          end.
        
        intros.
        unfold t0s0, t1s1.
       (** x ~ y **)
       (**x~ x' and y~y', x' ~ y' **)
        (** replace the first voters' nonce (nonce 0) with a fresh nonce (nonce 20) **)
        Axiom cca2Trans: forall {m} {l1 l2 l1' l2': mylist m}, l1'~l2' /\ l1 ~ l1' /\ l2 ~ l2' -> l1 ~ l2.
       unfold do0, dv0.
       unfold s0. unfold e00.
       Axiom dummy: forall {n} (z z': mylist n), z ~ z'.
       pose proof(dummy  [msg b00, msg b11,
                       msg
                         (If (acc00) & acc11
                          then (e00,
                                 (e11,
                                   If (dist fphi02) & (pvchecks fphi02)
                                  then If ! (isin pv00 (pi1 (d 1 fphi02), (pi1 (d 2 fphi02), pi1 (d 3 fphi02))))
                                  then shufl (pi1 (d 1 fphi02)) (pi1 (d 2 fphi02)) (pi1 (d 3 fphi02))
                                       else O
                                  else |_),
                                 (l00,
                                   (l11,
                                     If (dist fphi05) &
                                       (pochecks fphi05) & ((isin k0 fphi05) & (isin k1 fphi05)) or ! ((isin k0 fphi05) or (isin k1 fphi05))
                                    then sotrm fphi05
                                    else |_)))
                          else |_)] (let phi02' := [msg b00, msg b11, msg {(c00, (ub c00 t r0 t2, nonce 20), TWO) }_ 11 ^^ 7 , msg e11] in
                                     let fphi02':= f (toListm phi02') in
                                     let s0' := (If (! (isin pv00 ((pi1 (d 1 fphi02')), ((pi1 (d 2 fphi02')), (pi1 (d 3 fphi02')))))) then (shufl (pi1 (d 1 fphi02')) (pi1 (d 2 fphi02')) (pi1 (d 3 fphi02'))) else O) in
                                     let dv0' :=  (If (dist fphi02') & (pvchecks fphi02') then s0' else |_) in
                                     let phi03':= phi02' ++ [msg (shufl (pi1 (d 1 fphi02')) (pi1 (d 2 fphi02')) (pi1 (d 3 fphi02')))] in
                                     let fphi03':= f (toListm phi03') in
                                     let l00' := (If (bnlcheck c00 (nonce 0) fphi03') then (enc ((label c00 fphi03'), (k0, THREE)) (pke 11) (er 9)) else O) in
                                     let l11' := (If (bnlcheck c11 (nonce 1) fphi03') then (enc ((label c11 fphi03'), (k1, THREE)) (pke 11) (er 10)) else O) in
                                     let phi05':= phi03' ++ [msg l00', msg l11'] in
                                     let fphi05':= f (toListm phi05') in
                                     let do0' := (If (dist fphi05')& (pochecks fphi05')& (((isink k0 fphi05')&(isink k1 fphi05')) or (! ((isink k0 fphi05')or (isink k1 fphi05')))) then (sotrm fphi05') else |_) in
                                     [msg b00, msg b11, msg (If (acc00) & acc11 then ( (enc (c00, (ub c00 t r0 t2, nonce 20), TWO) (pke 11) (er 9)) , (e11, dv0'), (l00', (l11', do0'))) else |_)])).
 unfold e10.
       assert( (let phi02' :=
          [msg b00, msg b11,
          msg {(c00, (ub c00 t r0 t2, nonce 20), TWO) }_ 11 ^^ 7,
          msg e11] in
                let fphi02' := f (toListm phi02') in
                let s0' :=
                  If ! (isin pv00
                             (pi1 (d 1 fphi02'), (pi1 (d 2 fphi02'), pi1 (d 3 fphi02'))))
                then shufl (pi1 (d 1 fphi02')) (pi1 (d 2 fphi02'))
                           (pi1 (d 3 fphi02'))
                else O in
                let dv0' := If (dist fphi02') & (pvchecks fphi02')
                then s0'
                else |_ in
                let phi03' :=
                  phi02' ++
                         [msg
                            (shufl (pi1 (d 1 fphi02')) (pi1 (d 2 fphi02'))
                                   (pi1 (d 3 fphi02')))] in
                let fphi03' := f (toListm phi03') in
                let l00' :=
                  If bnlcheck c00 (nonce 0) fphi03'
                then (enc (label c00 fphi03', (k0, THREE)) (pke 11) (er 9))
                else O in
                let l11' :=
                  If bnlcheck c11 (nonce 1) fphi03'
                then (enc (label c11 fphi03', (k1, THREE)) (pke 11) (er 10))
                else O in
                let phi05' := phi03' ++ [msg l00', msg l11'] in
                let fphi05' := f (toListm phi05') in
                let do0' :=
                  If (dist fphi05') &
                    (pochecks fphi05') &
                    ((isink k0 fphi05') & (isink k1 fphi05')) (*or
             ! ((isink k0 fphi05') or (isink k1   fphi05')) *)
                then sotrm fphi05'
                else |_ in
                [msg b00, msg b11,
                  msg
                    (If (acc00) & acc11
                     then ((enc (c00, (ub c00 t r0 t2, nonce 20), TWO) (pke 11) (er 9)),
                            (e11, dv0'), (l00', (l11', do0')))
                     else |_)]) ~
                                (let phi12' :=
                                   [msg b10, msg b01,
                                     msg {(c10, (ub c10 t r0 t4, nonce 20), TWO) }_ 11 ^^ 7,
                                     msg e01] in
                                 let fphi12' := f (toListm phi12') in
                                 let s1' :=
                                   If ! (isin pv10
                                              (pi1 (d 1 fphi12'), (pi1 (d 2 fphi12'), pi1 (d 3 fphi12'))))
                                 then shufl (pi1 (d 1 fphi12')) (pi1 (d 2 fphi12'))
                                            (pi1 (d 3 fphi12'))
                                 else O in
                                 let dv1' := If (dist fphi12') & (pvchecks fphi12')
                                 then s1'
                                 else |_ in
                                 let phi13' :=
                                   phi12' ++
                                          [msg
                                             (shufl (pi1 (d 1 fphi12')) (pi1 (d 2 fphi12'))
                                                    (pi1 (d 3 fphi12')))] in
                                 let fphi13' := f (toListm phi13') in
                                 let l10' :=
                                   If bnlcheck c10 (nonce 0) fphi13'
                                 then (enc (label c10 fphi13', (k0, THREE)) (pke 11) (er 9))
                                 else O in
                                 let l01' :=
                                   If bnlcheck c10 (nonce 1) fphi13'
                                 then (enc (label c10 fphi13', (k1, THREE)) (pke 11) (er 10))
                                 else O in
                                 let phi15' := phi13' ++ [msg l10', msg l01'] in
                                 let fphi15' := f (toListm phi15') in
                                 let do1' :=
                                   If (dist fphi15') &
                                     (pochecks fphi15') &
                                     ((isink k0 fphi15') & (isink k1 fphi15')) (* or
             ! ((isink k0 fphi15') or (isink k1 fphi15')) *)
                                 then sotrm fphi15'
                                 else |_ in
                                 [msg b10, msg b01,
                                   msg
                                     (If (acc10) & acc01
                                      then ((enc (c10, (ub c10 t r0 t4, nonce 20), TWO) (pke 11) (er 9)),
                                             (e01, dv1'), (l10', (l01', do1')))
                                      else |_)])).
        simpl.
        Import ListNotations.
        assert( (ncheck (nonce 0) (f
                                     [b10; b01; (enc (c10, (ub c10 t r0 t4, nonce 20), TWO) (pke 11) (er 7)); e01;
                                      shufl (pi1 (d 1 (f [b10; b01; (enc (c10, (ub c10 t r0 t4, nonce 20), TWO) (pke 11) (er 7)); e01])))
                                            (pi1 (d 2 (f [b10; b01; (enc (c10, (ub c10 t r0 t4, nonce 20), TWO) (pke 11) (er 7)); e01])))
                                            (pi1 (d 3 (f [b10; b01; (enc (c10, (ub c10 t r0 t4, nonce 20), TWO) (pke 11) (er 7)); e01])))]))%list ## FAlse).
        unfold ncheck.
        unfold isin.

Lemma tau1: forall x y z, (tau 1 (x, (y, z))) # x.
Proof. intros. unfold tau. rewrite proj1; auto. reflexivity.
Qed.
Lemma tau2: forall x y z, (tau 2 (x, (y, z))) # y.
Proof. intros. unfold tau; rewrite proj2, proj1;auto. reflexivity. Qed.
Lemma tau3: forall x y z, (tau 3 (x, (y, z))) # z.
Proof. intros. unfold tau. repeat rewrite proj2; try reflexivity.
Qed.
(*Eval compute in FAlse or TRue. *)
rewrite tau1, tau2, tau3.

        Axiom freshneq: forall (n : nat) (m : message),
       ^? (m) = true  -> Fresh (cons n nil) [msg m] = true ->
       ([bol (nonce n) #? m]) ~ [bol FAlse].
simpl.
pose proof(freshneq 0 (pi2
      (pi2
         (pi2
            (pi1
               (f
                  [b10; b01; (enc (c10, (ub c10 t r0 t4, nonce 20), TWO) (pke 11) (er 7));
                  e01;
                  shufl
                    (pi1
                       (d 1
                          (f
                             [b10; b01;
                             (enc (c10, (ub c10 t r0 t4, nonce 20), TWO) (pke 11) (er 7));
                             e01])))
                    (pi1
                       (d 2
                          (f
                             [b10; b01;
                             (enc (c10, (ub c10 t r0 t4, nonce 20), TWO) (pke 11) (er 7));
                             e01])))
                    (pi1
                       (d 3
                          (f
                             [b10; b01;
                             (enc (c10, (ub c10 t r0 t4, nonce 20), TWO) (pke 11) (er 7));
                             e01])))])))))).
simpl in H8.

simpl in H1. rewrite andb_true_iff in H1. inversion H1.
repeat rewrite H9 in H8.
unfold t4, t5 in H8.
 rewrite  clos_sub_vtrm in H8;auto.
 rewrite  clos_sub_vtrm in H8;auto.
repeat rewrite andb_true_r, andb_true_l in H8.
 unfold Fresh in H8, H6.  simpl in H8, H6.
 (** ********)
 assert( occur_name_msg 0 t = false).
destruct (occur_name_msg 0 t). simpl in H6.
inversion H6. reflexivity.
assert( occur_name_msg 0 t2 = false).
destruct (occur_name_msg 0 t2).
simpl in H6. rewrite H11 in H6. simpl in H6. inversion H6. reflexivity.
assert( occur_name_msg 0 t3 = false).
destruct (occur_name_msg 0 t3).
simpl in H6. rewrite H12 in H6. simpl in H6. inversion H6. rewrite H11. reflexivity. reflexivity.
assert( occur_name_msg 0 t4 = false).
destruct (occur_name_msg 0 t4).
simpl in H6. rewrite H11, H12, H13 in H6. simpl in H6. inversion H6. reflexivity.
assert( occur_name_msg 0 t5 = false).
destruct (occur_name_msg 0 t5).
simpl in H6. rewrite H11, H12, H13, H14 in H6. simpl in H6. inversion H6. reflexivity.
fold t4 in H8.
rewrite H11, H14, H15 in H8. simpl in H8.
Axiom consteql: forall x f, const_bol f = true -> [bol x]~[bol f] -> x ## f.
assert( (const_bol FAlse) = true). reflexivity.
apply consteql in H8; auto.
rewrite H8.
(** prove N0 is fresh in tau2 of the decrypted message **)


pose proof(freshneq 0 (pi2
      (pi2
         (pi2
            (pi1
               (pi2 (f
                  [b10; b01; (enc (c10, (ub c10 t r0 t4, nonce 20), TWO) (pke 11) (er 7));
                  e01;
                  shufl
                    (pi1
                       (d 1
                          (f
                             [b10; b01;
                             (enc (c10, (ub c10 t r0 t4, nonce 20), TWO) (pke 11) (er 7));
                             e01])))
                    (pi1
                       (d 2
                          (f
                             [b10; b01;
                             (enc (c10, (ub c10 t r0 t4, nonce 20), TWO) (pke 11) (er 7));
                             e01])))
                    (pi1
                       (d 3
                          (f
                             [b10; b01;
                             (enc (c10, (ub c10 t r0 t4, nonce 20), TWO) (pke 11) (er 7));
                             e01])))]))))))).
simpl in H17.

repeat rewrite H9 in H17.
unfold t4, t5 in H17.
 rewrite  clos_sub_vtrm in H17;auto.
 rewrite  clos_sub_vtrm in H17;auto. simpl in H17.
 unfold Fresh in H17; simpl in H17.
 fold t4 in H17.
 rewrite H11, H14, H15 in H17. simpl in H17.



apply consteql in H17; auto.
rewrite H17.
clear H8 H17.

pose proof(freshneq 0 (pi2 (pi2 (pi2 (pi2 (pi2 (f
                  [b10; b01; (enc (c10, (ub c10 t r0 t4, nonce 20), TWO) (pke 11) (er 7));
                  e01;
                  shufl
                    (pi1
                       (d 1
                          (f
                             [b10; b01;
                             (enc (c10, (ub c10 t r0 t4, nonce 20), TWO) (pke 11) (er 7));
                             e01])))
                    (pi1
                       (d 2
                          (f
                             [b10; b01;
                             (enc (c10, (ub c10 t r0 t4, nonce 20), TWO) (pke 11) (er 7));
                             e01])))
                    (pi1
                       (d 3
                          (f
                             [b10; b01;
                             (enc (c10, (ub c10 t r0 t4, nonce 20), TWO) (pke 11) (er 7));
                             e01])))]))))))).
simpl in H8.
unfold t4, t5 in H8.
 rewrite  clos_sub_vtrm in H8;auto.
 rewrite  clos_sub_vtrm in H8;auto. simpl in H8.
repeat rewrite H9 in H8. simpl in H8.
unfold Fresh in H8; simpl in H8.
fold t4 in H8.
rewrite H11, H14, H15 in H8. simpl in H8.
apply consteql in H8; auto.
rewrite H8; clear H8; auto.
unfold orB.
 repeat rewrite IFFALSE_B. reflexivity.
  (left;inversion H4; unfold distMvars; simpl; try rewrite H17; try rewrite H18; try reflexivity).
(left;inversion H4; unfold distMvars; simpl; try rewrite H17; try rewrite H18; try rewrite H19; try reflexivity).
(left;inversion H4; unfold distMvars; simpl; try rewrite H17; try rewrite H18; try rewrite H19; try reflexivity).
(left;inversion H4; unfold distMvars; simpl; try rewrite H17; try rewrite H18; try rewrite H19; try reflexivity).
(left;inversion H4; unfold distMvars; simpl; try rewrite H17; try rewrite H18; try rewrite H19; try rewrite H11; try rewrite H12; try reflexivity).
(left;inversion H4; unfold distMvars; simpl; try rewrite H17; try rewrite H18; try rewrite H19; try rewrite H11; try rewrite H12; try reflexivity).

(*******************************************)
assert( let x:= (enc (c10, (ub c10 t r0 t4, nonce 20), TWO) (pke 11) (er 7)) in (bnlcheck c10 (nonce 0)
                  (f
                     [b10; b01; x; e01;
                     shufl (pi1 (d 1 (f [b10; b01; x; e01])))
                       (pi1 (d 2 (f [b10; b01; x; e01])))
                       (pi1 (d 3 (f [b10; b01; x; e01])))])) ## FAlse).
simpl. unfold bnlcheck.
rewrite H8. repeat rewrite andB_FAlse_r; try reflexivity.
rewrite H9.
rewrite IFFALSE_M.
clear H8 H9.
(********************************************)

assert( let x:= (enc (c00, (ub c00 t r0 t2, nonce 20), TWO) (pke 11) (er 7)) in  (bnlcheck c00 (nonce 0)
                    (f
                       [b00; b11; x; e11;
                       shufl (pi1 (d 1 (f [b00; b11; x; e11])))
                         (pi1 (d 2 (f [b00; b11; x; e11])))
                         (pi1 (d 3 (f [b00; b11; x; e11])))])) ## FAlse).
 unfold bnlcheck.
unfold ncheck. unfold isin.
rewrite tau1, tau2, tau3.
pose proof( freshneq 0 (let x:= (enc (c00, (ub c00 t r0 t2, nonce 20), TWO) (pke 11) (er 7)) in (tau 3 (pi2 (tau 1 (f
                       [b00; b11; x; e11;
                       shufl (pi1 (d 1 (f [b00; b11; x; e11])))
                         (pi1 (d 2 (f [b00; b11; x; e11])))
                         (pi1 (d 3 (f [b00; b11; x; e11])))])))))).
simpl in H8.
unfold t2, t3 in H8.
 rewrite  clos_sub_vtrm in H8;auto.
 rewrite  clos_sub_vtrm in H8;auto. simpl in H8.
simpl in H1.
simpl in H1. rewrite andb_true_iff in H1. inversion H1.
repeat rewrite H9 in H8.
simpl in H8.
unfold Fresh in H8, H6; simpl in H8, H6.
assert( occur_name_msg 0 t = false).
destruct (occur_name_msg 0 t). simpl in H6.
inversion H6. reflexivity.
assert( occur_name_msg 0 t2 = false).
destruct (occur_name_msg 0 t2).
simpl in H6. rewrite H11 in H6. simpl in H6. inversion H6. reflexivity.
assert( occur_name_msg 0 t3 = false).
destruct (occur_name_msg 0 t3).
simpl in H6. rewrite H12 in H6. simpl in H6. inversion H6. rewrite H11. reflexivity. reflexivity.
fold t2 in H8.
rewrite H11, H12, H13 in H8. simpl in H8.
apply consteql in H8; auto; try  (left;inversion H4; unfold distMvars; simpl; try rewrite H16; try rewrite H17; try rewrite H18; try rewrite H19; try reflexivity).
Axiom extcomphid: forall {n} (z z': mylist n), z ~ z'.
(******)
pose proof( freshneq 0 (let x:= (enc (c00, (ub c00 t r0 t2, nonce 20), TWO) (pke 11) (er 7)) in (tau 3 (pi2 (tau 2 (f
                       [b00; b11; x; e11;
                       shufl (pi1 (d 1 (f [b00; b11; x; e11])))
                             (pi1 (d 2 (f [b00; b11; x; e11])))
                             (pi1 (d 3 (f [b00; b11; x; e11])))])))))).
simpl in H14.
rewrite H9 in H14.
unfold t2, t3 in H14.
 rewrite  clos_sub_vtrm in H14;auto.
 rewrite  clos_sub_vtrm in H14;auto. simpl in H14.
unfold Fresh in H14. simpl in H14.
fold t2 in H14.
rewrite H11, H12, H13 in H14. simpl in H14.
apply consteql in H14; auto; try (left;inversion H4; unfold distMvars; simpl; try rewrite H16; try rewrite H17; try rewrite H18; try rewrite H19; try reflexivity).
(*******************************)
pose proof(freshneq 0 (let x:= (enc (c00, (ub c00 t r0 t2, nonce 20), TWO) (pke 11) (er 7)) in (tau 3 (pi2 (tau 3 (f
                       [b00; b11; x; e11;
                       shufl (pi1 (d 1 (f [b00; b11; x; e11])))
                             (pi1 (d 2 (f [b00; b11; x; e11])))
                             (pi1 (d 3 (f [b00; b11; x; e11])))])))))).
simpl in H15.
rewrite H9 in H15.
unfold t2, t3 in H15.
 rewrite  clos_sub_vtrm in H15;auto.
 rewrite  clos_sub_vtrm in H15;auto. simpl in H15.
unfold Fresh in H15, H6. simpl in H15, H6.
fold t2 in H15.
rewrite H11, H12, H13 in H15. simpl in H15.
apply consteql in H15; auto; try (left; try inversion H4; unfold distMvars; simpl; try rewrite H16; try rewrite H17; try reflexivity).
rewrite H8, H14, H15. unfold orB. repeat rewrite IFFALSE_B. simpl.
repeat rewrite andB_FAlse_r; try reflexivity.
(left;inversion H4; unfold distMvars; simpl; try rewrite H16; try rewrite H17; try rewrite H18; try rewrite H19; try reflexivity).
(left;inversion H4; unfold distMvars; simpl; try rewrite H16;  try rewrite H17; try rewrite H18; try rewrite H19; try reflexivity).
(left;inversion H4; unfold distMvars; simpl; try rewrite H16;  try rewrite H17; try rewrite H18; try rewrite H19; try reflexivity).
(left;inversion H4; unfold distMvars; simpl; try rewrite H15;  try rewrite H16; try rewrite H18; try rewrite H19; try reflexivity).
(left;inversion H4; unfold distMvars; simpl; try rewrite H9;  try rewrite H10; try rewrite H17; try rewrite H18; try rewrite H19; try reflexivity).
(left;inversion H4; unfold distMvars; simpl; try rewrite H9;  try rewrite H10; try rewrite H17; try rewrite H18; try rewrite H19; try reflexivity). rewrite H8.
rewrite IFFALSE_M.
unfold isink.
unfold k0.
(** we need to prove that the attacker cannot compute the commitment key **)
pose proof (ENCCCA2).
Axiom infeasible_comp_ck: forall n t g, (closMsg t) = true ->
                                          (** (distMvars [msg t']) = (cons m nil) ->  I can prove this:Fresh (cons n nil) [msg t, msg t'] = true **) ((g t) #? (kc (nonce n)))  ## FAlse.
(*** I will prove this later **) unfold b00.
        (*Eval compute in b00. *)
Search eqm.        
(* Axiom eqm_sym: forall m1 m2, (m1 #? m2) ## (m2 #? m1). *)
        repeat rewrite eqCom.Example14_M' with (m1:= (kc (nonce 3))).
repeat rewrite infeasible_comp_ck with (n:= 3); auto.
unfold orB.
repeat rewrite IFFALSE_B.
repeat rewrite andB_FAlse_l.  repeat rewrite andB_FAlse_r. repeat rewrite IFFALSE_M. simpl.
(** we replace the encryption that emits *)
(*         aply_ifbr. simpl. repeat unfold acc00, acc11, acc10, acc01. *)
(*         Axiom instantiate: forall n n' c00 c11 t r0 r1 t0, ({{ n := (bl c00 t r0) }} ({{ n':=(bl c11 t r1) }} t0)) # ((bl c00 t r0), (bl c11 t r1)). unfold t2, t3, t4, t5; repeat try rewrite instantiate. *)
(*         aplyDestrComm. simpl. *)
(*         Axiom destCommAbsTerm: forall t, destrCommMsg t t = mypair (cons (msg t) nil) (cons (msg t) nil). simpl. *)
(*         repeat rewrite destCommAbsTerm. simpl. unfold mylength. simpl. *)
(*         2:{ *)
(*           simpl. rewrite destCommAbsTerm. simpl. *)
(*         unfold mylength. simpl. *)
       
(*         Goal destrCommMsg t2 t4 = mypair (cons (msg |_) nil) (cons (msg |_) nil). *)
(* 2:{ repeat rewrite destCommAbsTerm. simpl. unfold r1. unfold r. unfold pi1ProdMylist. *)
(* simpl. *)
    pose proof(compHid_ext).
        
apply extcomphid.

 simpl.
simpl in H1;
rewrite andb_true_iff in H1;
inversion H1;
rewrite H10; unfold t4, t5; repeat rewrite clos_sub_vtrm;try left; inversion H4; unfold distMvars; simpl; try rewrite H12; try rewrite H13; try reflexivity.

simpl.
simpl in H1;
rewrite andb_true_iff in H1;
inversion H1;
rewrite H10; unfold t4, t5; repeat rewrite clos_sub_vtrm;try left; inversion H4; unfold distMvars; simpl; try rewrite H12; try rewrite H13; try reflexivity.

simpl.
simpl in H1;
rewrite andb_true_iff in H1;
inversion H1;
rewrite H10; unfold t4, t5; repeat rewrite clos_sub_vtrm;try left; inversion H4; unfold distMvars; simpl; try rewrite H12; try rewrite H13; try reflexivity.


  simpl.
simpl in H1;
rewrite andb_true_iff in H1;
inversion H1;
rewrite H10; unfold t2, t3; repeat rewrite clos_sub_vtrm;try left; inversion H4; unfold distMvars; simpl; try rewrite H12; try rewrite H13; try reflexivity.



simpl.
simpl in H1;
rewrite andb_true_iff in H1;
inversion H1;
rewrite H10; unfold t2, t3; repeat rewrite clos_sub_vtrm;try left; inversion H4; unfold distMvars; simpl; try rewrite H12; try rewrite H13; try reflexivity.

simpl.
simpl in H1;
rewrite andb_true_iff in H1;
inversion H1;
rewrite H10; unfold t2, t3; repeat rewrite clos_sub_vtrm;try left; inversion H4; unfold distMvars; simpl; try rewrite H12; try rewrite H13; try reflexivity.
apply extcomphid.
Qed.

End lemma_25.
