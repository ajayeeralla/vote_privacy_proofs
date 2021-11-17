 (************************************************************************)
(* Copyright (c) 2017-2018, Ajay Kumar Eeralla <ae266@mail.missouri.edu>*) 
(************************************************************************)   
Require Export auxDefs.
(* Module aux. *)
(*   Export destructTerm. *)
(*   Fixpoint submsg_bol pk r (t': message)(s: message) (b: Bool): Bool := *)
(*     match b with *)
(*     | eqb  b1 b2 =>  (eqb (submsg_bol pk r t' s b1) (submsg_bol pk r t' s b2)) *)
(*     | eqm t1 t2 => (eqm (submsg_msg pk r t' s t1) (submsg_msg pk r t' s t2)) *)
(*     | ifb_then_else_ t1 t2 t3 => (IF (submsg_bol pk r t' s t1) then (submsg_bol pk r t' s t2) else (submsg_bol pk r t' s t3)) *)
(*     | ver t1 t2 t3 => ver (submsg_msg pk r t' s t1) (submsg_msg pk r t' s t2) (submsg_msg pk r t' s t3) *)
(*     | bver t1 t2 t3 => bver (submsg_msg pk r t' s t1) (submsg_msg pk r t' s t2) (submsg_msg pk r t' s t3) *)
(*     | acc t1 t2 t3 t4 => acc (submsg_msg pk r t' s t1) (submsg_msg pk r t' s t2) (submsg_msg pk r t' s t3) (submsg_msg pk r t' s t4) *)
(*     | _ => b *)
(*     end *)
(*   with submsg_msg pk r (t': message)(s: message) (t: message): message := *)
(*          match t with *)
(*          | enc t1 t2 t3 => match t2, t3 with *)
(*                            | pi1 (ke (nonce n1)), re (nonce n2) => if ((n1 =? pk)%nat && (n2 =? r)%nat)&& message_beq t1 t' *)
(*                                                                    then enc s t2 t3 else t *)
(*                            | _, _ => t *)
(*                            end *)
(*          | _ => t *)

(*          end. *)

(*   Fixpoint submsg_os pk r (t': message) (s: message) (os: oursum): oursum := *)
(*     match os with *)
(*     | msg t => msg (submsg_msg pk r t' s t) *)
(*     | bol b => bol (submsg_bol pk r t' s b) *)
(*     end. *)

(*   Fixpoint submsgMylist pk r (t': message) (s: message) {n} (ml: mylist n): mylist n := *)
(*     match ml with *)
(*     | [] => [] *)
(*     | h:t => (submsg_os pk r t' s h): submsgMylist pk r t' s t *)
(*     end. *)

(*   (* Replace nonce directly as the above definition seems slow  *) *)
(*   Fixpoint repNonceBol n n' b: Bool := *)
(*   match b with *)
(*     | eqb  b1 b2 =>  (eqb (repNonceBol n n' b1) (repNonceBol n n' b2)) *)
(*     | eqm t1 t2 => (eqm (repNonceMsg n n' t1) (repNonceMsg n n' t2)) *)
(*     | ifb_then_else_ t1 t2 t3 => (IF (repNonceBol n n' t1) then (repNonceBol n n' t2) else (repNonceBol n n' t3)) *)
(*     | ver t1 t2 t3 => ver  (repNonceMsg n n' t1) (repNonceMsg n n' t2) (repNonceMsg n n' t3) *)
(*     | bver t1 t2 t3 => bver (repNonceMsg n n' t1) (repNonceMsg n n' t2) (repNonceMsg n n' t3) *)
(*     | acc t1 t2 t3 t4 => acc (repNonceMsg n n' t1) (repNonceMsg n n' t2) (repNonceMsg n n' t3) (repNonceMsg n n' t4) *)
(*     | _ => b *)
(*   end *)
(* with repNonceMsg n n' t: message := *)
(*        match t with *)
(*          | nonce k => if (k =? n)%nat then (nonce n') else t *)
(*          | ifm_then_else_ b1 t1 t2 =>    (If (repNonceBol n n' b1) then (repNonceMsg n n' t1) else (repNonceMsg n n' t2)) *)
(*          | pair t1 t2 => pair (repNonceMsg n n' t1) (repNonceMsg n n' t2) *)
(*          | pi1 t1 =>  pi1 (repNonceMsg n n' t1) *)
(*          | pi2 t1 =>  pi2 (repNonceMsg n n' t1) *)
(*          | L t1 =>  L (repNonceMsg n n' t1) *)
(*          | to t1 => to  (repNonceMsg n n' t1) *)
(*          | f l =>  (f (@map message message  (repNonceMsg n n') l)) *)
(*          (** foo function symbol *) *)
(*          (** FOO syntax *) *)
(*          (** Vote values *) *)
(*          | V0 t1 => V0 (repNonceMsg n n' t1) *)
(*          | V1 t1 => V1 (repNonceMsg n n' t1) *)
(*          (** Public Key *) *)
(*          | pubkey t1 => pubkey (repNonceMsg n n' t1) *)
(*          (** Commitments *) *)
(*          | kc t1 => kc (repNonceMsg n n' t1) *)
(*          | comm t1 t2 => comm (repNonceMsg n n' t1) (repNonceMsg n n' t2) *)
(*          | open t1 t2 t3 => open (repNonceMsg n n' t1) (repNonceMsg n n' t2) (repNonceMsg n n' t3) *)
(*          (** Shuffling *) *)
(*          | shufl t1 t2 t3 =>  shufl (repNonceMsg n n' t1) (repNonceMsg n n' t2) (repNonceMsg n n' t3) *)
(*          (** Encryptions *) *)
(*          | ke t1 => ke (repNonceMsg n n' t1) *)
(*          | re t1 => re (repNonceMsg n n' t1) *)
(*          | enc t1 t2 t3 =>  enc (repNonceMsg n n' t1) (repNonceMsg n n' t2) (repNonceMsg n n' t3) *)
(*          | dec t1 t2 =>  dec (repNonceMsg n n' t1) (repNonceMsg n n' t2) *)
(*            (** Blind Signatures *) *)
(*          | kb t1 => kb (repNonceMsg n n' t1) *)
(*          | rb t1 => rb (repNonceMsg n n' t1) *)
(*          | bsign t1 t2 t3 =>  bsign (repNonceMsg n n' t1) (repNonceMsg n n' t2) (repNonceMsg n n' t3) *)
(*          | bl t1 t2 t3 =>  bl (repNonceMsg n n' t1) (repNonceMsg n n' t2) (repNonceMsg n n' t3) *)
(*          | ub t1 t2 t3 t4 => ub (repNonceMsg n n' t1) (repNonceMsg n n' t2)  (repNonceMsg n n' t3)   (repNonceMsg n n' t4) *)
(*          (** Signatures *) *)
(*          | ks t1 => ks (repNonceMsg n n' t1) *)
(*          | rs t1 => rs (repNonceMsg n n' t1) *)
(*          | sign t1 t2 t3 => sign (repNonceMsg n n' t1) (repNonceMsg n n' t2) (repNonceMsg n n' t3) *)
(*          (* | z t1 => z t1 *) *)
(*          | compl t1 => compl (repNonceMsg n n' t1) *)
(*          (** all other constrs *) *)
(*          | _ => t *)
(*        end. *)

(*   Fixpoint repNonceOs n n' os: oursum := *)
(*     match os with *)
(*     | msg t => msg (repNonceMsg n n' t) *)
(*     | bol b => bol (repNonceBol n n' b) *)
(*     end. *)

(*   Fixpoint repNonceMylist n n' {m} (l: mylist m): mylist m := *)
(*     match l with *)
(*     | [] => [] *)
(*     | h:t => (repNonceOs n n' h) : (repNonceMylist n n' t) *)
(*     end. *)
(* End aux. *)

(* Section lemma_25. *)

(*   Definition V (b:bool) := *)
(*     match b with *)
(*     | false => (V0 (nonce 0)) *)
(*     | true => (V1 (nonce 0)) *)
(*     end. *)

(*   Definition cn (b:bool) :nat := *)
(*     match b with *)
(*     | false => 0 *)
(*     | true => 1 *)
(*     end. *)


(*   Open Scope msg_scope. *)

  (** **)
(* Axiom isinCong: forall m1 m2 m3 m4, m1 # m2 -> m3 # m4 -> (isin m1 m3) ## (isin m2 m4). *)
(* Add Parametric Morphism: (@isin) with *)
(*     signature EQm ==> EQm ==> EQb as isin_mor. *)
(* Proof. intros. apply isinCong; try intuition. Qed. *)

(* The following frame is useful when we apply CCA2 axiom *)
Definition z0 := phi0 ++ [msg lbl, msg (kc (nonce 3)), msg (kc (nonce 4)), msg (r 1), msg (r 2), msg pk (* public key AD*), msg (sr 14), msg (sr 15), msg (nonce 20), msg (nonce 21), msg (er 7), msg (er 8), msg (er 9), msg (er 10)].
Arguments z0: simpl never.

Import ListNotations.
(* Check if a an elment of type mylist m is a sublist of mylist n without actually converting to oslist *)
Fixpoint checkSublist {m} (l1: mylist m){n}(l2: mylist n): bool :=
  if (m <=? n)%nat then
           match l1 with
           | [] => true
           | h:t => if (checkostmylis h l2) then (checkSublist t l2) else false
           end
  else false.
(* Occurrence indices vector *)
Fixpoint subListPosVec {m} (l1: mylist m) {n} (l2: mylist n): Nlist:=
  match (checkSublist l1 l2), l1 with
  | true, h:t => (eltPos h l2)::(subListPosVec t l2)
  | _, _ => [ ]
  end.

Axiom funcAppAttComp: forall {n} (l1 l2: mylist n) {m}(lm1 lm2: mylist m), l1 ~ l2 ->
                                                                           ((checkSublist lm1 l1) && (checkSublist lm2 l2) = true)%bool ->
                                                                           (subListPosVec lm1 l1) = (subListPosVec lm2 l2) ->
                                                                           (l1 ++ [msg (f (toListm lm1))]) ~ (l2 ++ [msg (f (toListm lm2))]).

Ltac tacFuncAppAttComp ml1 ml2 H:=
  apply funcAppAttComp with (lm1:= ml1) (lm2:= ml2) in H. 

(** Given index vector retrieve sulist that constitutes elements of the positions *)

Fixpoint getSublist (l: Nlist) {n} (ml: mylist n): mylist (length l):=
  match l with
  | [ ] => []
  | h::t => (getelt_at_pos h ml): getSublist t ml
  end.
Axiom funcAppAttComp': forall pl {n} (l1 l2: mylist n), l1 ~ l2 -> ([msg (f (toListm (getSublist pl l1)))]++l1) ~ ([msg (f (toListm (getSublist pl l2)))] ++ l2).
(* Build frame phi03 *)
Ltac tacFuncAppAttComp' l H :=
  apply funcAppAttComp' with (pl:= l) in H; simpl in H.

(* Check hypothesis type which will be useful in computing an elt position in mylist manually *)
Ltac chkType H :=
  match goal with
  | [H:?X ~ ?Y |- _ ] => let t:= type of X in idtac t "~" t
  end.

Axiom funcAppFmb: forall (p:nat) {n} (ml1 ml2 : mylist n) {f}, (ml1 ~ ml2) -> ([bol (f (ostomsg (getelt_at_pos p ml1)))] ++ ml1) ~
                                                                                                                                 ([bol (f (ostomsg (getelt_at_pos p ml2)))] ++ ml2).
Ltac tacFuncAppFmb g n H :=
  apply funcAppFmb with (f:= g) (p:= n) in H; simpl in H.
(* Useful to add same nonce, Vars on both sides *)
Axiom funAppNatMsg: forall (m: nat) f {n} (ml1 ml2: mylist n), ml1 ~ ml2 -> ([msg (f m)] ++ ml1) ~ ([msg (f m)] ++ ml2).
Ltac tacFunAppNatMsg g n H:=
  apply funAppNatMsg with (f:= g) (m:=n) in H; simpl in H.
(** Simplified CCA2 axiom **)
Axiom ENCCCA2': forall (n1 n2 n3: nat) (u u': message) {m} (l: mylist m),
    (|u|#?|u'|) ## TRue ->
    (* (List.length (distMvars l) <=? 1) = true -> *)
    (closMylist ([msg u, msg u'] ++ l) = true) ->
    (* cca2compmylis n n1 u u' l = true -> *)
    (l++[msg {u}_n1^^n2]) ~ (l++ [msg {u'}_n1^^n3]).

Axiom bnlcheckFailForNonce: forall n t1 t2, closMsg t2 = true -> Fresh (cons n nil) [msg t2] = true -> (bnlcheck t1 (nonce n) t2) ## FAlse.

Add Parametric Morphism :(@bnlcheck) with
    signature EQm ==> EQm ==> EQm ==> EQb as bnlcheck_mor.
Proof. intros; aply_cong; auto. Qed.

Ltac rewBnlchkFailNonce c n1 :=
  repeat match goal with
         |[|- context[bnlcheck c (nonce n1) _] ]=> rewrite bnlcheckFailForNonce with (n:= n1) (t1:= c); try unfold Fresh; simpl; intuition
         end.

Fixpoint and (l: list bool): bool :=
  match l with
  | [ ] => false
  | h::t => h || and t
  end.

Axiom isinkFalse: forall n l, let k := kc (nonce n) in
                              let l' := map (message_beq k) l in
                              and l' = false ->
                              (isink k (f l)) ## FAlse.
Ltac tacIsinkFalse n1 :=
  repeat match goal with
         | [|- context[isink (kc (nonce n1)) ?X] ] => rewrite isinkFalse with (n:= n1); try auto
         end.

(* Require Import Coq.Lists.List. *)
Lemma rep_first_ballot:
      let v0 := V0 (f (toListm phi0)) in
      let v1 := V1 (f (toListm phi0)) in
      (* (| v0 |) #? (| v1 |) ## TRue -> *)
      (vcheck v0) & (vcheck v1) ## TRue ->
      (* let v0 := V0 (nonce 0) in *)
      (* let v1 := V1 (nonce 0) in *)
      (* (| v0 |) #? (| v1 |) ## TRue -> *)
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
      (* (occur_name_mylist 100 [msg t, msg t0, msg t1] = false) -> *)
      (* (Fresh (cons 0 nil) [msg t, msg t2, msg t3, msg t4, msg t5] = true) -> *)
      [msg b00, msg b11, msg t0s0] ~ [msg b10, msg b01, msg t1s1].
Proof. intros.
       (* unfold t0s0, t1s1. unfold dv0, dv1. unfold s0, s1. *)
       (* rewrite ifMorphIfThen.  repeat rewrite ifMorphPair2.     rewrite ifMorphPair1.  rewrite ifMorphIfThen. *)
       (* unfold l00. *)
       (* unfold bnlcheck. *)
       (* unfold ncheck. *)
       (* aply_ifbr. *) 
    
       aply_cca2Trans (let e00' := (enc ((c00, ((ub c00 t r0 t2), (nonce 150))), TWO) (pke 11) (er 7)) in
                       let phi02':= [msg b00, msg b11, msg e00', msg e11] in
                       let fphi02':= f (toListm phi02') in
                       let s0':= (If (! (isin pv00 ((pi1 (d 1 fphi02')), ((pi1 (d 2 fphi02')), (pi1 (d 3 fphi02')))))) then (shufl (pi1 (d 1 fphi02')) (pi1 (d 2 fphi02')) (pi1 (d 3 fphi02'))) else O)in
                       let dv0' := (If (dist fphi02') & (pvchecks fphi02') then s0' else |_) in
                       let phi03':= phi02' ++[msg dv0'] in
                       let fphi03' := f (toListm phi03') in
                       let l00' := (If (bnlcheck c00 (nonce 20) fphi03') then (enc ((label c00 fphi03'), (k0, THREE)) (pke 11) (er 9)) else O) in
                       let l11' := (If (bnlcheck c11 (nonce 21) fphi03') then (enc ((label c11 fphi03'), (k1, THREE)) (pke 11) (er 10)) else O) in
                       let phi05':= phi03'++[msg l00', msg l11'] in
                       let fphi05' := f (toListm phi05') in
                       let do0' := (If (dist fphi05') & (pochecks fphi05') & (((isink k0 fphi05') & (isink k1 fphi05'))) (* or (! ((isink k0 fphi05')or (isink k1 fphi05'))))*) then (sotrm fphi05') else |_) in
                       let t0s0' := (If acc00 & acc11 then ((e00', (e11, dv0')), (l00', (l11', do0'))) else |_) in
                       [msg b00, msg b11, msg t0s0'])
                       (let e10' := (enc ((c10, ((ub c10 t r0 t4), (nonce 150))), TWO) (pke 11) (er 7)) in
                        let phi12':= [msg b10, msg b01, msg e10', msg e01] in
                        let fphi12':= f (toListm phi12') in
                        let s1' := (If (! (isin pv10 ((pi1 (d 1 fphi12')), ((pi1 (d 2 fphi12')), (pi1 (d 3 fphi12')))))) then (shufl (pi1 (d 1 fphi12')) (pi1 (d 2 fphi12')) (pi1 (d 3 fphi12'))) else O)in
                        let dv1' := (If (dist fphi12') & (pvchecks fphi12') then s1' else |_) in
                        let phi13':= phi12' ++[msg dv1'] in
                        let fphi13' := f (toListm phi13') in
                        let l10' := (If (bnlcheck c10 (nonce 20) fphi13') then (enc ((label c10 fphi13'), (k0, THREE)) (pke 11) (er 9)) else O) in
                        let l01' := (If (bnlcheck c01 (nonce 21) fphi13') then (enc ((label c01 fphi13'), (k1, THREE)) (pke 11) (er 10)) else O) in
                        let phi15':= phi13'++[msg l10', msg l01'] in
                        let fphi15' := f (toListm phi15') in
                        let do1' := (If (dist fphi15')& (pochecks fphi15')& (((isink k0 fphi15')&(isink k1 fphi15')))(* or (! ((isink k0 fphi15')or (isink k1 fphi15'))))*) then (sotrm fphi15') else |_) in
                        let t1s1' := (If acc10 & acc01 then ((e10', (e01, dv1')), (l10', (l01', do1'))) else |_) in
                        [msg b10, msg b01, msg t1s1']).

                                                                                               (* replace nonce in the encryption term of the left frame using CCA2, L ~ L'  *)
       pose proof (let n1:= 11 in
                   let n2:= 7 in
                   let n3:= 7 in
                   let u:= ((c00, ((ub c00 t r0 t2), (nonce 20))), TWO) in
                   let u':= ((c00, ((ub c00 t r0 t2), (nonce 150))), TWO) in
                   let zAdd:= [msg c00, msg c11, msg b00, msg b11,  bol (acc00&acc11), msg pv00, msg pv11, msg e11] in
                   ENCCCA2' n1 n2 n3 u u' zAdd).
       simpl in H0.
       simpl in H0.
       tacFuncAppAttComp phi02 [msg b00, msg b11, msg {((c00, ((ub c00 t r0 t2), (nonce 150))), TWO)}_11^^7, msg e11] H0; try auto.
       simpl in H0.
       (** To apply FUNCApp *)
       funapp_f1_in (d 1) 10 H0.
       funapp_f1_in (d 2) 11 H0.
       funapp_f1_in (d 3) 12 H0.
       do 3 funapp_f1_in pi1 3 H0.
       funapp_f2m_in pair 2 1 H0.
       funapp_f2m_in pair 4 1 H0.
       funapp_f2b_in isin 15 1 H0.
       funapp_notB_in 1 H0.
       funapp_f3m_in shufl 7 6 5 H0.
       funapp_fm_in O H0.
       funapp_f3bm_in ifm_then_else_ 3 2 1 H0.
     
       tacFuncAppFmb pvchecks 23 H0.
       tacFuncAppFmb dist 24 H0.
       funapp_andB_in 1 2 H0.
       funapp_fm_in |_ H0.
       funapp_f3bm_in ifm_then_else_ 2 5 1 H0.
       tacFuncAppAttComp' [21; 22; 27; 26; 1] H0.
     
       tacFunAppNatMsg nonce 20 H0.
       
       funapp_f3mb_in bnlcheck 21 1 2 H0.
       tacFunAppNatMsg nonce 21 H0.
       funapp_f3mb_in bnlcheck 24 1 4 H0.
       (* Add k0 *)
       tacFunAppNatMsg nonce 3 H0.
       funapp_f1_in kc 1 H0.
       restr_proj_in 2 H0.
       funapp_fm_in THREE H0.
       funapp_f2m_in pair 2 1 H0.
       tacFunAppNatMsg nonce 4 H0.
       funapp_f1_in kc 1 H0.
       restr_proj_in 2 H0.
       funapp_f2m_in pair 1 3 H0.
       restr_proj_in 4 H0.
       funapp_f2m_in label 29 9 H0.
       funapp_f2m_in pair 1 2 H0.
       do 2 restr_proj_in 2 H0.
       funapp_f2m_in label 28 9 H0.
       funapp_f2m_in pair 1 4 H0.
       restr_proj_in 2 H0.
       restr_proj_in 4 H0.
       tacFunAppNatMsg pke 11 H0.
       tacFunAppNatMsg er 9 H0.
       funapp_f3m_in enc 3 2 1 H0.
       restr_proj_in 2 H0.
       restr_proj_in 3 H0. 
       tacFunAppNatMsg er 10 H0.
       funapp_f3m_in enc 4 3 1 H0.
       restr_proj_in 5 H0.
       restr_proj_in 4 H0.
       restr_proj_in 2 H0.
       restr_proj_in 6 H0.
       restr_proj_in 8 H0.
       funapp_fm_in O H0.
       funapp_f3bm_in ifm_then_else_ 6 2 1 H0. 
       do 2 restr_proj_in 2 H0.
       restr_proj_in 5 H0. 
       restr_proj_in 6 H0.
       funapp_fm_in O H0.
       funapp_f3bm_in ifm_then_else_ 6 3 1 H0.
       restr_proj_in 2 H0.
       restr_proj_in 3 H0.
       restr_proj_in 5 H0. 
       do 18 restr_proj_in 6 H0.
       chkType H0. 
       tacFuncAppAttComp' [7;8; 13; 12; 5; 1; 2] H0.
       tacFuncAppFmb dist 1 H0.
       tacFuncAppFmb pochecks 2 H0. 
       funapp_f2b_in isin 7 3 H0.
       funapp_f2b_in isin 7 4 H0.
       funapp_andB_in 4 3 H0.
       funapp_andB_in 1 3 H0.
       restr_proj_in 2 H0.
       funapp_andB_in 1 2 H0.
       restr_proj_in 2 H0.
       do 4 restr_proj_in 2 H0.
       funapp_f1_in sotrm 2 H0.
       restr_proj_in 3 H0.
       funapp_fm_in |_ H0. 
       funapp_f3bm_in ifm_then_else_ 3 2 1 H0.
       do 3 restr_proj_in 2 H0.
       chkType H0.
       restr_proj_in 12 H0.
       restr_proj_in 11 H0.
       restr_proj_in 7 H0.
       restr_proj_in 5 H0.
       restr_proj_in 4 H0.
       funapp_f2m_in pair 3 1 H0.
       restr_proj_in 2 H0.
       restr_proj_in 3 H0.
       funapp_f2m_in pair 2 1 H0.
       do 2 restr_proj_in 2 H0.
       chkType H0.  
       funapp_f2m_in pair 6 2 H0.
         funapp_f2m_in pair 8 1 H0.
       restr_proj_in 2 H0.
       funapp_f2m_in pair 1 2 H0.
       do 3 restr_proj_in 2 H0.
       funapp_fm_in |_ H0.
       funapp_f3bm_in ifm_then_else_ 5 2 1 H0.
       restrsublis H0; try auto.
       repeat (try apply len_reg; try rewrite eqmeql; try apply nameEql; try simpl; try intuition).
       (* ********************* *)
       (* replace nonce in the encryption term of the right frame using CCA2, R ~ R'  *)
       (* ************************ *)
       split. 
       pose proof (let n1:= 11 in
                   let n2:= 7 in
                   let n3:= 7 in
                   let u:= (c10, (ub c10 t r0 t4, nonce 20), TWO) in
                   let u':=(c10, (ub c10 t r0 t4, nonce 150), TWO) in
                   let zAdd:= [msg c10, msg c01, msg b10, msg b01,  bol (acc10) & acc01, msg pv10, msg pv01, msg e01] in
                   ENCCCA2' n1 n2 n3 u u' zAdd).
       simpl in H0.
       simpl in H0.
       tacFuncAppAttComp phi12 [msg b10, msg b01, msg {(c10, (ub c10 t r0 t4, nonce 150), TWO)}_11^^7, msg e01] H0; try auto.
       simpl in H0.
       (** To apply FUNCApp *)
       funapp_f1_in (d 1) 10 H0.
       funapp_f1_in (d 2) 11 H0.
       funapp_f1_in (d 3) 12 H0.
       do 3 funapp_f1_in pi1 3 H0.
       funapp_f2m_in pair 2 1 H0.
       funapp_f2m_in pair 4 1 H0.
       funapp_f2b_in isin 15 1 H0.
       funapp_notB_in 1 H0.
       funapp_f3m_in shufl 7 6 5 H0.
       funapp_fm_in O H0.
       funapp_f3bm_in ifm_then_else_ 3 2 1 H0.
     
       tacFuncAppFmb pvchecks 23 H0.
       tacFuncAppFmb dist 24 H0.
       funapp_andB_in 1 2 H0.
       funapp_fm_in |_ H0.
       funapp_f3bm_in ifm_then_else_ 2 5 1 H0.
       tacFuncAppAttComp' [21; 22; 27; 26; 1] H0.
     
       tacFunAppNatMsg nonce 20 H0.
       
       funapp_f3mb_in bnlcheck 21 1 2 H0.
       tacFunAppNatMsg nonce 21 H0.
       funapp_f3mb_in bnlcheck 24 1 4 H0.
       (* Add k0 *)
       tacFunAppNatMsg nonce 3 H0.
       funapp_f1_in kc 1 H0.
       restr_proj_in 2 H0.
       funapp_fm_in THREE H0.
       funapp_f2m_in pair 2 1 H0.
       tacFunAppNatMsg nonce 4 H0.
       funapp_f1_in kc 1 H0.
       restr_proj_in 2 H0.
       funapp_f2m_in pair 1 3 H0.
       restr_proj_in 4 H0.
       funapp_f2m_in label 29 9 H0.
       funapp_f2m_in pair 1 2 H0.
       do 2 restr_proj_in 2 H0.
       funapp_f2m_in label 28 9 H0.
       funapp_f2m_in pair 1 4 H0.
       restr_proj_in 2 H0.
       restr_proj_in 4 H0.
       tacFunAppNatMsg pke 11 H0.
       tacFunAppNatMsg er 9 H0.
       funapp_f3m_in enc 3 2 1 H0.
       restr_proj_in 2 H0.
       restr_proj_in 3 H0. 
       tacFunAppNatMsg er 10 H0.
       funapp_f3m_in enc 4 3 1 H0.
       restr_proj_in 5 H0.
       restr_proj_in 4 H0.
       restr_proj_in 2 H0.
       restr_proj_in 6 H0.
       restr_proj_in 8 H0.
       funapp_fm_in O H0.
       funapp_f3bm_in ifm_then_else_ 6 2 1 H0. 
       do 2 restr_proj_in 2 H0.
       restr_proj_in 5 H0. 
       restr_proj_in 6 H0.
       funapp_fm_in O H0.
       funapp_f3bm_in ifm_then_else_ 6 3 1 H0.
       restr_proj_in 2 H0.
       restr_proj_in 3 H0.
       restr_proj_in 5 H0. 
       do 18 restr_proj_in 6 H0.
       chkType H0. 
       tacFuncAppAttComp' [7;8; 13; 12; 5; 1; 2] H0.
       tacFuncAppFmb dist 1 H0.
       tacFuncAppFmb pochecks 2 H0. 
       funapp_f2b_in isin 7 3 H0.
       funapp_f2b_in isin 7 4 H0.
       funapp_andB_in 4 3 H0.
       funapp_andB_in 1 3 H0.
       restr_proj_in 2 H0.
       funapp_andB_in 1 2 H0.
       restr_proj_in 2 H0.
       do 4 restr_proj_in 2 H0.
       funapp_f1_in sotrm 2 H0.
       restr_proj_in 3 H0.
       funapp_fm_in |_ H0. 
       funapp_f3bm_in ifm_then_else_ 3 2 1 H0.
       do 3 restr_proj_in 2 H0.
       chkType H0.
       restr_proj_in 12 H0.
       restr_proj_in 11 H0.
       restr_proj_in 7 H0.
       restr_proj_in 5 H0.
       restr_proj_in 4 H0.
       funapp_f2m_in pair 3 1 H0.
       restr_proj_in 2 H0.
       restr_proj_in 3 H0.
       funapp_f2m_in pair 2 1 H0.
       do 2 restr_proj_in 2 H0.
       chkType H0.  
       funapp_f2m_in pair 6 2 H0.
         funapp_f2m_in pair 8 1 H0.
       restr_proj_in 2 H0.
       funapp_f2m_in pair 1 2 H0.
       do 3 restr_proj_in 2 H0.
       funapp_fm_in |_ H0.
       funapp_f3bm_in ifm_then_else_ 5 2 1 H0.
       restrsublis H0; try auto.
       repeat (try apply len_reg; try rewrite eqmeql; try apply nameEql; try simpl; try intuition).
       (* ********************************** *)
       (*   *********************************************************** *)
       (*   Done replacing nonce 20 using CCA2  *)
       (* Only need to prove the leftover goal *)
       simpl. 
       
        (* This can be proved using unforgeCommitKey *) 
       (* Prove nonce 20 isn't there in the attacker's computation *) 
       assert(let e00' := (enc ((c00, ((ub c00 t r0 t2), (nonce 150))), TWO) (pke 11) (er 7)) in
                                                                     let phi02':= [msg b00, msg b11, msg e00', msg e11] in
       let fphi02':= f (toListm phi02') in
       let s0':= (If (! (isin pv00 ((pi1 (d 1 fphi02')), ((pi1 (d 2 fphi02')), (pi1 (d 3 fphi02')))))) then (shufl (pi1 (d 1 fphi02')) (pi1 (d 2 fphi02')) (pi1 (d 3 fphi02'))) else O)in
       let dv0' := (If (dist fphi02') & (pvchecks fphi02') then s0' else |_) in
       let phi03':= phi02' ++[msg dv0'] in
                                                                                                                          let fphi03' := f (toListm phi03') in
       fphi03' # (If (dist fphi02') & (pvchecks fphi02') then (If (! (isin pv00 ((pi1 (d 1 fphi02')), ((pi1 (d 2 fphi02')), (pi1 (d 3 fphi02'))))))
       then (f (toListm (phi02'++[msg (shufl (pi1 (d 1 fphi02')) (pi1 (d 2 fphi02')) (pi1 (d 3 fphi02')))]))) else (f (toListm (phi02'++[msg O])))) else (f (toListm (phi02'++[msg |_]))))).
 simpl.

Ltac tacIfMorphComp:=
  repeat match goal with
         | [|- context[f ?X] ] => rewrite ifMorphAttComp with (l:=X); simpl; try intuition
         end.
  Ltac rewAndBFalse :=
  repeat match goal with
         | [|- context [ FAlse & _ ] ] => rewrite andB_FAlse_l
         | [|- context [ _ & FAlse ] ] => rewrite andB_FAlse_r
         end; redg.
 Ltac tacIfMorphPair :=
         match goal with
         |[|- context[ (If ?B then ?T1 else ?T2, ?T3)] ] => rewrite (@ifMorphPair1 B T1 T2 T3)
         |[|- context[ (?T1, If ?B then ?T2 else ?T3)] ] => rewrite (@ifMorphPair2 B T1 T2 T3)
         end.
       tacIfMorphComp.
       
       simpl in H0. simpl.  
       assert(let e00' := (enc ((c00, ((ub c00 t r0 t2), (nonce 150))), TWO) (pke 11) (er 7)) in
              let phi02':= [msg b00, msg b11, msg e00', msg e11] in
              let fphi02':= f (toListm phi02') in
              let s0':= (If (! (isin pv00 ((pi1 (d 1 fphi02')), ((pi1 (d 2 fphi02')), (pi1 (d 3 fphi02')))))) then (shufl (pi1 (d 1 fphi02')) (pi1 (d 2 fphi02')) (pi1 (d 3 fphi02'))) else O)in
              let dv0' := (If (dist fphi02') & (pvchecks fphi02') then s0' else |_) in
              let phi03':= phi02' ++[msg dv0'] in
              let fphi03' := f (toListm phi03') in
              (bnlcheck c00 (nonce 20) fphi03') ## (bnlcheck c00 (nonce 20) (If (dist fphi02') & (pvchecks fphi02')
                                                                             then If ! (isin pv00
                                                                                             (pi1 (d 1 fphi02'),
                                                                                               (pi1 (d 2 fphi02'), pi1 (d 3 fphi02'))))
                                                                             then f
                                                                                    (toListm
                                                                                       (phi02' ++
                                                                                               [msg
                                                                                                  (shufl (pi1 (d 1 fphi02'))
                                                                                                         (pi1 (d 2 fphi02')) 
                                                                                                         (pi1 (d 3 fphi02')))])) 
                                                                                  else f (toListm (phi02' ++ [msg O])) 
                                                                             else f (toListm (phi02' ++ [msg |_]))))).
       simpl.
       rewrite H0; reflexivity.  clear H0.
       simpl in H1.
       repeat rewrite ifMorphf3 in H1.
       repeat rewrite H1. simpl. clear H1.
      rewBnlchkFailNonce c00 20. repeat redg.
       unfold k0.
       tacIsinkFalse 3. 
       rewAndBFalse.
       (*************Do the same steps on right side ********)
       (* ******************************************************** *) 
       assert(let e10' := (enc ((c10, ((ub c10 t r0 t4), (nonce 150))), TWO) (pke 11) (er 7)) in
              let phi12':= [msg b10, msg b01, msg e10', msg e01] in
              let fphi12':= f (toListm phi12') in
              let s1' := (If (! (isin pv10 ((pi1 (d 1 fphi12')), ((pi1 (d 2 fphi12')), (pi1 (d 3 fphi12'))))))
                          then (shufl (pi1 (d 1 fphi12')) (pi1 (d 2 fphi12')) (pi1 (d 3 fphi12'))) else O) in
              let dv1' := (If (dist fphi12') & (pvchecks fphi12') then s1' else |_) in
              let phi13':= phi12' ++[msg dv1'] in
              let fphi13' := f (toListm phi13') in
              fphi13' # (If (dist fphi12') & (pvchecks fphi12') then
                           (If (! (isin pv10 ((pi1 (d 1 fphi12')), ((pi1 (d 2 fphi12')), (pi1 (d 3 fphi12'))))))
                            then (f (toListm (phi12'++[msg (shufl (pi1 (d 1 fphi12')) (pi1 (d 2 fphi12')) (pi1 (d 3 fphi12')))])))
                            else (f (toListm (phi12'++[msg O])))) else (f (toListm (phi12'++[msg |_]))))).
       simpl.
       tacIfMorphComp.
       simpl in H0. 
       assert(let e10' := (enc ((c10, ((ub c10 t r0 t4), (nonce 150))), TWO) (pke 11) (er 7)) in
              let phi12':= [msg b10, msg b01, msg e10', msg e01] in
              let fphi12':= f (toListm phi12') in
              let s1' := (If (! (isin pv10 ((pi1 (d 1 fphi12')), ((pi1 (d 2 fphi12')), (pi1 (d 3 fphi12'))))))
                          then (shufl (pi1 (d 1 fphi12')) (pi1 (d 2 fphi12')) (pi1 (d 3 fphi12'))) else O) in
              let dv1' := (If (dist fphi12') & (pvchecks fphi12') then s1' else |_) in
              let phi13':= phi12' ++[msg dv1'] in
              let fphi13' := f (toListm phi13') in
              (bnlcheck c10 (nonce 20) fphi13') ## (bnlcheck c10 (nonce 20) (If (dist fphi12') & (pvchecks fphi12')
                                                                             then If ! (isin pv10
                                                                                             (pi1 (d 1 fphi12'),
                                                                                               (pi1 (d 2 fphi12'), pi1 (d 3 fphi12'))))
                                                                             then f
                                                                                    (toListm
                                                                                       (phi12' ++
                                                                                               [msg
                                                                                                  (shufl (pi1 (d 1 fphi12'))
                                                                                                         (pi1 (d 2 fphi12')) 
                                                                                                         (pi1 (d 3 fphi12')))])) 
                                                                                  else f (toListm (phi12' ++ [msg O])) 
                                                                             else f (toListm (phi12' ++ [msg |_]))))).
       simpl.
       rewrite H0. reflexivity. clear H0.
       simpl in H1.
       repeat rewrite ifMorphf3 in H1.
       repeat rewrite H1; clear H1.
       rewBnlchkFailNonce c10 20. repeat redg. 
      
       unfold k0.
       tacIsinkFalse 3.
       rewAndBFalse.
       simpl.                                                                                                         
        
       (** apply ifbranch repeatedly **)
       repeat aply_ifbr.
       repeat (try tacIfMorphPair; try aply_ifbr). simpl.
       all: let n:= numgoals in idtac n "goals".
       7:{
         aplyDestrComm; apply nodup; simpl; try unfold c10, k0; try aplyCompHid. }.
       (* Ltac unfold_proj_pair := *)
        aplyDestrComm; apply nodup; simpl; try unfold c10, k0; try aplyCompHid.
        
       aplyDestrComm; apply nodup; simpl; try unfold c10, k0; try aplyCompHid.

       aplyDestrComm; apply nodup; simpl; try unfold c10, k0; try aplyCompHid.
       aplyDestrComm; apply nodup; simpl; try unfold c10, k0; try aplyCompHid.
       aplyDestrComm; apply nodup; simpl; try unfold c10, k0; try aplyCompHid.
       aplyDestrComm; apply nodup; simpl; try unfold c10, k0; try aplyCompHid.
