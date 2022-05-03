(************************************************************************)
(* Copyright (c) 2017-2018, Ajay Kumar Eeralla <ae266@mail.missouri.edu>*)
(************************************************************************)
Require Export newCca2Compliant.
Import ListNotations.

(** Simplified CCA2 axiom **)
(* Axiom ENCCCA2': forall (n1 n2 n3: nat) (u u': message) {m} (l: mylist m), *)
(*     (|u|#?|u'|) ## TRue -> *)
(*     (* (List.length (distMvars l) <=? 1) = true -> *) *)
(*     (closMylist ([msg u, msg u'] ++ l) = true) -> *)
(*     (* cca2compmylis n n1 u u' l = true -> *) *)
(*     (l++[msg {u}_n1^^n2]) ~ (l++ [msg {u'}_n1^^n3]). *)

(* This should be provable from freshNeq *)
Axiom bnlcheckFailForNonce: forall n t1 t2, closMsg t2 = true ->
                                            Fresh (cons n nil) [msg t2] = true ->
                                            (bnlcheck t1 (nonce n) t2) ## FAlse.

Ltac rewBnlchkFailNonce c n1 :=
  repeat match goal with
         | [|- context[bnlcheck c (nonce n1) _] ] => rewrite bnlcheckFailForNonce with (n:= n1) (t1:= c);
                                                      try unfold Fresh; simpl; intuition
         end.

Fixpoint and (l: list bool): bool :=
  match l with
  | [ ] => false
  | h::t => h || and t
  end.

(* This should be provable from unforgeCommitKey *)
Axiom isinkFalse: forall n l, let k := kc (nonce n) in
                              let l' := map (message_beq k) l in
                              and l' = false -> (isink k (f l)) ## FAlse.
Ltac tacIsinkFalse n1 :=
  repeat match goal with
         | [|- context[isink (kc (nonce n1)) ?X] ] => rewrite isinkFalse with (n:= n1); try auto
         end.

Ltac rewAndBFalse :=
  repeat match goal with
         | [|- context [ FAlse & _ ] ] => rewrite andB_FAlse_l
         | [|- context [ _ & FAlse ] ] => rewrite andB_FAlse_r
         end; redg.


Axiom ifMorphMsg: forall f b t1 t2, f (If b then t1 else t2) # (If b then (f t1) else (f t2)).
Axiom ifMorphBol: forall f b t1 t2, f (If b then t1 else t2)  ## (IF b then (f t1) else (f t2)).

Import CxtCompHid.

Axiom funcAppRestr: forall p1 p2 {m} (l1 l2: mylist m) {f: message -> message -> oslist},
    (IsContextOslist f) ->
    l1 ~ l2 ->
    let osl1:= (f (ostomsg (getelt_at_pos p1 l1)) (ostomsg (getelt_at_pos p2 l1))) in
    let osl2:= (f (ostomsg (getelt_at_pos p1 l2)) (ostomsg (getelt_at_pos p2 l2))) in
    let y := oslToMylist osl1 osl2 in
    ((mylength y) =? 0 = false)%nat -> (pi1ProdMylist y) ~ (pi2ProdMylist y).

Import cca2Compliant.

Fixpoint occur_name_oslist (x:nat) (l: oslist) :bool :=
  match l with
    | [ ] => false
    | h :: ml1 =>  (occurOs x h) || (occur_name_oslist x ml1)
  end.

Axiom cca2CxtAxiom: forall n n1 n2 u u' {f: message -> oslist},
    (|u| #? |u'|) ## TRue ->
    (IsContextCCA2Oslist n f) ->
    occur_name_oslist n1 (f O) = false ->
    occur_name_oslist n2 (f O) = false ->
    let osl1:= (f {u}_n^^n1) in
    let osl2:= (f {u'}_n^^n2) in
    let y := oslToMylist osl1 osl2 in
    ((mylength y) =? 0 = false)%nat -> (pi1ProdMylist y) ~ (pi2ProdMylist y).

Axiom funcAppRestrCompHid: forall n1 n2 v0 v1 {f: message -> message -> oslist},
    let ml:= [msg v0, msg v1] in
    occur_name_mylist n1 ml = false ->
    occur_name_mylist n2 ml = false ->
    IsContextOslist f ->
    let c00:= (comm v0 (kc (nonce n1))) in
    let c11:= (comm v1 (kc (nonce n2))) in
    let c10:= (comm v1 (kc (nonce n1))) in
    let c01:= (comm v0 (kc (nonce n2))) in
    [msg c00, msg c11 ] ~ [msg c10, msg c01] ->
    let osl1:= (f c00 c11) in
    let osl2:= (f c10 c01) in
    let y := oslToMylist osl1 osl2 in
    ((mylength y) =? 0 = false)%nat -> (pi1ProdMylist y) ~ (pi2ProdMylist y).

Axiom simplifyGoal: forall {n m o} (l: mylist n) (l1 l2: mylist m) {g: mylist m -> mylist o}, (l ++ l1) ~ (l ++ l2) -> (l ++ (g l1)) ~ (l ++ (g l2)).

Axiom funcApp_t0_t1 : forall n m p1 p2 t0 t1 {n1} (l1 l2: mylist n1), l1 ~ l2 ->
               let s0 := ostomsg (getelt_at_pos p1 l1) in
               let s1 := ostomsg (getelt_at_pos p2 l1) in
               let s0' := ostomsg (getelt_at_pos p1 l2) in
               let s1' := ostomsg (getelt_at_pos p2 l2) in
               (l1 ++ [msg ({{ n := s0 }} ({{ m := s1 }} t0)), msg ({{ n := s0 }} ({{ m := s1 }} t1))]) ~  (l2 ++ [msg ({{ n := s0' }} ({{ m := s1' }} t0)), msg ({{ n := s0' }} ({{ m := s1' }} t1))]).

Add Parametric Morphism: (@ isin) with
           signature EQm ==> EQm ==> EQb as isin_mor.
       Proof. intros; aply_cong; try auto. Qed.

Lemma rep_first_ballot:
      let v0 := V0 (f (toListm phi0)) in
      let v1 := V1 (f (toListm phi0)) in
      (vcheck v0) & (vcheck v1) ## TRue ->  (*  which implies (| v0 |) #? (| v1 |) ## TRue -> *)

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
      let t2 := ({{ 5 := b00 }} ({{ 6:= b11 }} t0)) in
      let t3 := ({{ 5 := b00 }} ({{ 6:= b11 }} t1)) in
      let acc00 := (acc c00 t r0 t2) in
      let acc11 := (acc c11 t r1 t3) in
      let pv00 := (c00, ((ub c00 t r0 t2), (nonce 20))) in
      let pv11 := (c11, ((ub c11 t r1 t3), (nonce 21))) in
      let e00 := (enc (pv00, TWO) (pke 11) (er 7)) in
      let e11 := (enc (pv11, TWO) (pke 11) (er 8)) in
      let phi02:= [msg b00, msg b11, msg e00, msg e11] in
      let fphi02:= f (toListm phi02) in
      let s0 := (If (! (isin pv00 ((pi1 (d 1 fphi02)), ((pi1 (d 2 fphi02)), (pi1 (d 3 fphi02))))))
                 then (shufl (pi1 (d 1 fphi02)) (pi1 (d 2 fphi02)) (pi1 (d 3 fphi02))) else O)in
      let dv0 := (If (dist fphi02) & (pvchecks fphi02) then s0 else |_) in
      let phi03:= phi02 ++[msg dv0] in
      let fphi03 := f (toListm phi03) in
      let l00 := (If (bnlcheck c00 (nonce 20) fphi03)
                  then (enc ((label c00 fphi03), (k0, THREE)) (pke 11) (er 9)) else O) in
      let l11 := (If (bnlcheck c11 (nonce 21) fphi03)
                  then (enc ((label c11 fphi03), (k1, THREE)) (pke 11) (er 10)) else O) in
      let phi05:= phi03++[msg l00, msg l11] in
      let fphi05 := f (toListm phi05) in
      let do0 := (If (dist fphi05) & (pochecks fphi05) & ((isink k0 fphi05) & (isink k1 fphi05)) (*or (! ((isink k0 fphi05)or (isink k1 fphi05))))*)
                  then (sotrm fphi05) else |_) in
      let t0s0 := (If acc00 & acc11 then ((e00, (e11, dv0)), (l00, (l11, do0))) else |_) in

      (* Right-side *)
      let c10 := (comm v1 k0) in
      let c01 := (comm v0 k1) in
      let b10 := (bl c10 t r0) in
      let b01 := (bl c01 t r1) in
      let t4 := ({{ 5 := b10 }} ({{ 6:= b01 }} t0)) in
      let t5 := ({{ 5 := b10 }} ({{ 6:= b01 }} t1)) in
      let acc10 := (acc c10 t r0 t4) in
      let acc01 := (acc c01 t r1 t5) in
      let pv10 := (c10, ((ub c10 t r0 t4), (nonce 20))) in
      let pv01 := (c01, ((ub c01 t r1 t5), (nonce 21))) in
      let e10 := (enc (pv10, TWO) (pke 11) (er 7)) in
      let e01 := (enc (pv01, TWO) (pke 11) (er 8)) in
      let phi12:= [msg b10, msg b01, msg e10, msg e01] in
      let fphi12:= f (toListm phi12) in
      let s1 := (If (! (isin pv10 ((pi1 (d 1 fphi12)), ((pi1 (d 2 fphi12)), (pi1 (d 3 fphi12)))))) then (shufl (pi1 (d 1 fphi12)) (pi1 (d 2 fphi12)) (pi1 (d 3 fphi12))) else O)in
      let dv1 := (If (dist fphi12) & (pvchecks fphi12) then s1 else |_) in
      let phi13:= phi12 ++ [msg dv1] in
      let fphi13 := f (toListm phi13) in
      let l10 := (If (bnlcheck c10 (nonce 20) fphi13) then (enc ((label c10 fphi13), (k0, THREE)) (pke 11) (er 9)) else O) in
      let l01 := (If (bnlcheck c01 (nonce 21) fphi13) then (enc ((label c01 fphi13), (k1, THREE)) (pke 11) (er 10)) else O) in
      let phi15:= phi13 ++[msg l10, msg l01] in
      let fphi15 := f (toListm phi15) in
      let do1 := (If (dist fphi15)& (pochecks fphi15)& (((isink k0 fphi15)&(isink k1 fphi15))) (*or (! ((isink k0 fphi15)or (isink k1 fphi15))))*) then (sotrm fphi15) else |_) in
      let t1s1 := (If acc10 & acc01 then ((e10, (e01, dv1)), (l10, (l01, do1))) else |_) in
      [msg b00, msg b11, msg t0s0] ~ [msg b10, msg b01, msg t1s1].
(*********Proof starts from here********)

Proof. intros.
       aply_cca2Trans (let e00' := (enc ((c00, ((ub c00 t r0 t2), (nonce 150))), TWO) (pke 11) (er 7)) in
                       let phi02':= [msg b00, msg b11, msg e00', msg e11] in
                       let fphi02':= f (toListm phi02') in
                       let dd n s :=  If (tau n s) #? e00' then (d n s) else (d n s) in
                       let s0':= (If (! (isin pv00 ((pi1 (dd 1 fphi02')), ((pi1 (dd 2 fphi02')), (pi1 (dd 3 fphi02')))))) then (shufl (pi1 (dd 1 fphi02')) (pi1 (dd 2 fphi02')) (pi1 (dd 3 fphi02'))) else O)in
                       let dv0' := (If (dist fphi02') & (pvchecks fphi02') then s0' else |_) in
                       let phi03':= phi02' ++[msg dv0'] in
                       let fphi03' := f (toListm phi03') in
                       let l00' := (If (bnlcheck c00 (nonce 20) fphi03') then (enc ((label c00 fphi03'), (k0, THREE)) (pke 11) (er 9)) else O) in
                       let l11' := (If (bnlcheck c11 (nonce 21) fphi03') then (enc ((label c11 fphi03'), (k1, THREE)) (pke 11) (er 10)) else O) in
                       let phi05':= phi03'++[msg l00', msg l11'] in
                       let fphi05' := f (toListm phi05') in
                       let p' n x := ( (tau 1 (dd n x)), (tau 2 (dd n x))) in
                       let sotrm' x := (shufl (p' 1 x) (p' 2 x) (p' 3 x)) in
                       let do0' := (If (dist fphi05') & (pochecks fphi05') & (((isink k0 fphi05') & (isink k1 fphi05')))(* or (! ((isink k0 fphi05')or (isink k1 fphi05'))))*) then (sotrm' fphi05') else |_) in
                       let t0s0' := (If acc00 & acc11 then ((e00', (e11, dv0')), (l00', (l11', do0'))) else |_) in
                       [msg b00, msg b11, msg t0s0'])

                      (let e10' := (enc ((c10, ((ub c10 t r0 t4), (nonce 150))), TWO) (pke 11) (er 7)) in
                        let phi12':= [msg b10, msg b01, msg e10', msg e01] in
                        let fphi12':= f (toListm phi12') in
                        let dd n s :=  If (tau n s) #? e10' then (d n s) else (d n s) in
                        let s1' := (If (! (isin pv10 ((pi1 (dd 1 fphi12')), ((pi1 (dd 2 fphi12')), (pi1 (dd 3 fphi12')))))) then (shufl (pi1 (dd 1 fphi12')) (pi1 (dd 2 fphi12')) (pi1 (dd 3 fphi12'))) else O)in
                        let dv1' := (If (dist fphi12') & (pvchecks fphi12') then s1' else |_) in
                        let phi13':= phi12' ++[msg dv1'] in
                        let fphi13' := f (toListm phi13') in
                        let l10' := (If (bnlcheck c10 (nonce 20) fphi13') then (enc ((label c10 fphi13'), (k0, THREE)) (pke 11) (er 9)) else O) in
                        let l01' := (If (bnlcheck c01 (nonce 21) fphi13') then (enc ((label c01 fphi13'), (k1, THREE)) (pke 11) (er 10)) else O) in
                        let phi15':= phi13'++[msg l10', msg l01'] in
                        let fphi15' := f (toListm phi15') in
                        let p' n x := ( (tau 1 (dd n x)), (tau 2 (dd n x))) in
                        let sotrm' x := (shufl (p' 1 x) (p' 2 x) (p' 3 x)) in
                        let do1' := (If (dist fphi15')& (pochecks fphi15')& (((isink k0 fphi15')&(isink k1 fphi15'))) (*or (! ((isink k0 fphi15')or (isink k1 fphi15'))))*) then (sotrm' fphi15') else |_) in
                        let t1s1' := (If acc10 & acc01 then ((e10', (e01, dv1')), (l10', (l01', do1'))) else |_) in
                          [msg b10, msg b01, msg t1s1']).
       Ltac rewDecs t n x n1 := rewrite <- (@IFSAME_M (t #? x) (dec t (ske n))) at n1.
       (* assert (forall n: nat, d n fphi02 # If (tau n fphi02) #? e00 then (pv00, TWO) else (If (tau n fphi02) #? e11 then (pv11, TWO) else (d n fphi02))). *)
       assert(forall (n:nat) (s:message), d n s # If (tau n s) #? e00 then (d n s) else (d n s)).
       intros.
       rewrite <- IFSAME_M with (b:= (tau n s) #? e00) at 1.
       reflexivity.
       unfold t0s0.
       (* rewrite left-side *)
       (* 2. rewrite decryptions in the opening phase  *)
       unfold do0, sotrm, p.
       Set Nested Proofs Allowed.
       Add Parametric Morphism n: (@tau n) with
           signature EQm ==> EQm as tau_mor.
       Proof. intros; aply_cong; try auto. Qed.
       rewrite H0 with (n:= 1) (s:= fphi05).
       rewrite H0 with (n:= 2) (s:= fphi05).
       rewrite H0 with (n:= 3) (s:= fphi05).
       (* 1. rewrite the decryptions in voting phase *)
       repeat unfold dv0, s0, l00, l11, do0, sotrm, p, fphi05, phi05, fphi03, phi03.
        rewrite H0 with (n:= 1) (s:= fphi02).
       rewrite H0 with (n:= 2) (s:= fphi02).
       rewrite H0 with (n:= 3) (s:= fphi02).

       (* Apply CCA2 definition using context *)
       pose proof (@cca2CxtAxiom 11 7 7 (pv00, TWO) ((c00, ((ub c00 t r0 t2), (nonce 150))), TWO)
                            (fun x => let e00' := x in
                                      let phi02':= [msg b00, msg b11, msg e00', msg e11] in
                                      let fphi02':= f (toListm phi02') in
                                      let dd n s :=  If (tau n s) #? e00 then (d n s) else (d n s) in
                             let s0':= (If (! (isin pv00 ((pi1 (dd 1 fphi02')), ((pi1 (dd 2 fphi02')), (pi1 (dd 3 fphi02')))))) then (shufl (pi1 (dd 1 fphi02')) (pi1 (dd 2 fphi02')) (pi1 (dd 3 fphi02'))) else O)in
                             let dv0' := (If (dist fphi02') & (pvchecks fphi02') then s0' else |_) in
                             let phi03':= phi02' ++[msg dv0'] in
                             let fphi03' := f (toListm phi03') in
                             let l00' := (If (bnlcheck c00 (nonce 20) fphi03') then (enc ((label c00 fphi03'), (k0, THREE)) (pke 11) (er 9)) else O) in
                             let l11' := (If (bnlcheck c11 (nonce 21) fphi03') then (enc ((label c11 fphi03'), (k1, THREE)) (pke 11) (er 10)) else O) in
                             let phi05':= phi03'++[msg l00', msg l11'] in
                             let fphi05' := f (toListm phi05') in
                             let p' n x := ( (tau 1 (dd n x)), (tau 2 (dd n x))) in
                             let sotrm' x := (shufl (p' 1 x) (p' 2 x) (p' 3 x)) in                                                     let do0' := (If (dist fphi05') & (pochecks fphi05') & (((isink k0 fphi05') & (isink k1 fphi05')))(* or (! ((isink k0 fphi05')or (isink k1 fphi05'))))*) then (sotrm' fphi05') else |_) in
                                                                                                                                       let t0s0' := (If acc00 & acc11 then ((e00', (e11, dv0')), (l00', (l11', do0'))) else |_) in
                                                                                                                                       [msg b00; msg b11; msg t0s0'])). simpl in H1. apply H1.
   msg
     (If (f [b00; b11; x]) #? x
         then (pv00, TWO)
      else dec (f [b00; b11; x]) (ske 11))])).
       rewr       (
       rewrite H0 with (n:= 1) (s:= (f (toListm [msg b00, msg b11, msg (enc ((c00, ((ub c00 t r0 t2), (nonce 150))), TWO) (pke 11) (er 7)), msg e11]))).

       rewrite <- (@IFSAME_M ((tau n fphi02) #? e11) (dec (tau n fphi02) (ske 11))) at 2.
       (** This should be proved using EQBRANCH *)
       Axiom rewEqBrDec: forall m1 m2 m3 m4: message, (If m1 #? m2 then dec m1 m3 else m4) # (If m1 #? m2 then (dec m2 m3) else m4).
       repeat rewrite rewEqBrDec.
       reflexivity.

       apply (@cca2CxtAxiom 11 7 7 (pv00, TWO) (pv00, TWO) (fun x => [msg b00; msg b11; msg x;
   msg
     (If (f [b00; b11; x]) #? x
         then (pv00, TWO)
      else dec (f [b00; b11; x]) (ske 11))])).

       Focus 2. constructor. unfold b00. repeat constructor. repeat constructor. Focus 2. reflexivity.      Focus 2. reflexivity. Focus 2. simpl. reflexivity.  apply len_reg. repeat apply eqmeql.
       apply eqmeql.
       assert (s0 # s0).
       unfold s0. unfold d.
       Set Nested Proofs Allowed.

       rewDecs (tau 1 fphi02) 11 e00 ((c00, ((ub c00 t r0 t2), (nonce 150))), TWO) ((c00, ((ub c00 t r0 t2), (nonce 150))), TWO).

       (* replace nonce in the encryption term of the left frame using CCA2, L ~ L' *)
       (* Axiom rewDecryption: forall n x e, dec x (ske n) # If x #? e then O else (dec x (ske n)). *)
       Fixpoint rewDecs n x (l: Mlist) : message :=
         match l with
         | [ ] => dec x (ske n)
         | h :: t => If x #? h then O else rewDecs n x t
         end.
       Axiom rewDecryption: forall n x l, dec x (ske n) # (rewDecs n x l).

       Ltac rewDecs n listEncs :=
       match goal with
       |[|- context[dec ?X (ske n)] ] => rewrite (@rewDecryption n X listEncs)
       end.
          match listEncs
       rewrite (@rewDecryption 11).
                       Axiom ENCCCA2: forall (n n1 n2 n3: nat) (u u': message) {m} (l: mylist m),
    (|u|#?|u'|) ## TRue ->
    (List.length (distMvars l) <=? 1) = true ->
    distMvars l = (cons n nil) ->
    (closMylist [msg u, msg u'] = true) ->
    ([ n <- {u}_n1^^n2 ] l) ~ ([ n <- {u'}_n1^^n3] l).
       pose proof (ENCCCA2 151 11 7 7 (c00, (ub c00 t r0 t2, nonce 20), TWO) (c00, (ub c00 t r0 t2, nonce 150), TWO)
                           (let e00' := (Mvar 151) in
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
                            let do0' := (If (dist fphi05') & (pochecks fphi05') & (((isink k0 fphi05') & (isink k1 fphi05')))(* or (! ((isink k0 fphi05')or (isink k1 fphi05'))))*) then (sotrm fphi05') else |_) in
                            let t0s0' := (If acc00 & acc11 then ((e00', (e11, dv0')), (l00', (l11', do0'))) else |_) in
                            [msg b00, msg b11, msg t0s0'])) as cca2.



         simpl in cca2.
                           If (acc00) & acc11
        then (e00', (e11, dv0'), (l00', (l11', do0')))
        else |_ in
   [msg b00, msg b11, msg t0s0']
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
       repeat (try apply len_reg; try rewrite eqmeql; try apply nameEql; try simpl; try intuition).*)
       (* ********************* *)
       (* replace nonce in the encryption term of the right frame using CCA2, R ~ R'  *)
       (* ************************ *)
       split.
       apply dummy.
(*       pose proof (let n1:= 11 in
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
       pose proof (let n1:= 11 in
                   let n2:= 7 in
                   let n3:= 7 in
                   let u:= ((c00, ((ub c00 t r0 t2), (nonce 20))), TWO) in
                   let u':= ((c00, ((ub c00 t r0 t2), (nonce 150))), TWO) in
                   (*let zAdd:= [msg c00, msg c11, msg b00, msg b11,  bol (acc00&acc11), msg pv00, msg pv11, msg e11] in*)
                   ENCCCA2' n1 n2 n3 u u' []) as cca2.
       simpl in cca2.
       apply funcAppRestr with (p1:=0) (p2:=1) (f:= (fun x y =>
                                                       (let e00' := y in
                                                        let c00 := (comm v0 k0) in
                                                        let c11 := (comm v1 k1) in
                                                        let phi02' := [msg b00, msg b11, msg e00', msg e11] in
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
                                                        let phi03' := phi02' ++ [msg dv0'] in
                                                        let fphi03' := f (toListm phi03') in
                                                        let l00' :=
                                                              If bnlcheck c00 (nonce 20) fphi03'
                                                        then (enc ((label c00 fphi03'), (k0, THREE)) (pke 11) (er 9))
                                                        else O in
                                                        let l11' :=
                                                          If bnlcheck c11 (nonce 21) fphi03'
                                                        then (enc ((label c11 fphi03'), (k1, THREE)) (pke 11) (er 10))
                                                        else O in
                                                        let phi05' := phi03' ++ [msg l00', msg l11'] in
                                                        let fphi05' := f (toListm phi05') in
                                                        let do0' :=     If (dist fphi05') &
                                                                          (pochecks fphi05') & (((isink k0 fphi05')&(isink k1 fphi05'))) (* or (! ((isink k0 fphi05')or (isink k1 fphi05'))))*)
                                                        then sotrm fphi05'
                                                        else |_ in
                                                        let t0s0' :=
                                                          If (acc00) & acc11
                                                        then (e00', (e11, dv0'), (l00', (l11', do0')))
                                                        else |_ in
                                                        [msg b00, msg b11, msg t0s0']))) in cca2.
       apply cca2. repeat (try apply len_reg; try rewrite eqmeql; try apply nameEql; simpl; intuition). auto.

       (* ********************* *)
       (* replace nonce in the encryption term of the right frame using CCA2, R ~ R'  *)
       (* ************************ *)
       split.
       pose proof (let n1:= 11 in
                   let n2:= 7 in
                   let n3:= 7 in
                   let u:= (c10, (ub c10 t r0 t4, nonce 20), TWO) in
                   let u':=(c10, (ub c10 t r0 t4, nonce 150), TWO) in
                   ENCCCA2' n1 n2 n3 u u' []) as cca2.
       simpl in cca2.

apply funcAppRestr with (p1:=0) (p2:=1) (f:= (fun x y =>
                                                           let c10 := (comm v1 k0) in
                                                           let c01 := (comm v0 k1) in
                                                           let e10' := y in
                                                           let phi12' := [msg b10, msg b01, msg e10', msg e01] in
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
                                                         let phi13' := phi12' ++ [msg dv1'] in
                                                         let fphi13' := f (toListm phi13') in
                                                         let l10' :=
                                                           If bnlcheck c10 (nonce 20) fphi13'
                                                         then (enc ((label c10 fphi13'), (k0, THREE)) (pke 11) (er 9))
                                                         else O in
                                                         let l01' :=
                                                           If bnlcheck c01 (nonce 21) fphi13'
                                                         then (enc ((label c01 fphi13'), (k1, THREE)) (pke 11) (er 10))
                                                         else O in
                                                         let phi15' := phi13' ++ [msg l10', msg l01'] in
                                                         let fphi15' := f (toListm phi15') in
                                                         let do1' :=
                                                           If (dist fphi15') &
                                                             (pochecks fphi15') & (((isink k0 fphi15')&(isink k1 fphi15'))) (*or (! ((isink k0 fphi15')or (isink k1 fphi15')))) *)
                                                         then sotrm fphi15'
                                                         else |_ in
                                                         let t1s1' :=
                                                           If (acc10) & acc01
                                                         then (e10', (e01, dv1'), (l10', (l01', do1')))
                                                         else |_ in
                                                         [msg b10, msg b01, msg t1s1'])) in cca2.
       simpl in cca2.
       apply cca2.  repeat (try apply len_reg; try rewrite eqmeql; try apply nameEql; simpl; intuition). auto.*)
       (* ********************************** *)
       (*   *********************************************************** *)
       (*   Done replacing nonce 20 using CCA2  *)
       (* Only need to prove the leftover goal *)
       (* This can be proved using unforgeCommitKey *)
       (* Prove nonce 20 isn't there in the attacker's computation *)
       simpl.

       repeat rewrite ifMorphMsg with (f := (fun x => let e00' := (enc ((c00, ((ub c00 t r0 t2), (nonce 150))), TWO) (pke 11) (er 7)) in (f [b00; b11;e00'; e11; x]))); intuition.
      repeat rewrite ifMorphBol.
       repeat match goal with
         | [|- context [label ?Y (If ?B then ?T1 else ?T2)] ] => rewrite ifMorphMsg with (f:= fun x => (label Y x))
        end.
       rewBnlchkFailNonce c00 20.
       repeat redg.
       unfold k0.
       tacIsinkFalse 3.
       rewAndBFalse.
       (*************Do the same steps on right side ********)
       (* ******************************************************** *)

       repeat rewrite ifMorphMsg with (f := (fun x => let e10' := (enc ((c10, ((ub c10 t r0 t4), (nonce 150))), TWO) (pke 11) (er 7)) in (f [b10; b01;e10'; e01; x]))); intuition.
      repeat rewrite ifMorphBol.
       repeat match goal with
         | [|- context [label ?Y (If ?B then ?T1 else ?T2)] ] => rewrite ifMorphMsg with (f:= fun x => (label Y x))
        end.
       rewBnlchkFailNonce c10 20.
       repeat redg.
       unfold k0.
       tacIsinkFalse 3.
       rewAndBFalse.


       Ltac rewOrBFalse :=
         repeat match goal with
                | [|- context [ FAlse or _ ] ] => rewrite orB_FAlse_l
                | [|- context [ _ or FAlse ] ] => rewrite orB_FAlse_r
                end; redg.
       rewOrBFalse.
       pose proof(compHid 3 4 v0 v1 []) as ch. simpl in ch.
       (*apply funcAppRestrCompHid with (n1:= 3) (n2:=4) (v0:= v0) (v1:= v1) (f:= fun x y => let b00 := (bl x t r0) in
                                                 let b11 := (bl y t r1) in
                                                 let t0 := (((vk 0), (Mvar 5), sign (Mvar 5) (ssk 0) (sr 14)), ((vk 1), (Mvar 6), sign (Mvar 6) (ssk 1) (sr 15))) in
                                                 let t1 := (t0, f (cons t0 nil)) in
                                                 let t2 := ({{ 5 := b00 }} ({{ 6:= b11 }} t0)) in
                                                 let t3 := ({{ 5 := b00 }} ({{ 6:= b11 }} t1)) in
                                                 let acc00 := (acc x t r0 t2) in
                                                 let acc11 := (acc y t r1 t3) in
                                                 let e00' := (enc ((x, ((ub x t r0 t2), (nonce 150))), TWO) (pke 11) (er 7)) in
                                                 let e11 := (enc ((y, ((ub y t r1 t3), (nonce 21))), TWO) (pke 11) (er 8)) in
                                                 let pv00 := (x, ((ub x t r0 t2), (nonce 20))) in
                                                 let pv11 := (y, ((ub y t r1 t3), (nonce 21))) in
                                                 let phi02':= [msg b00, msg b11, msg e00', msg e11] in
                                                 let fphi02':= f (toListm phi02') in
                                                 [msg b00; msg b11; msg (If (acc00) & acc11
                                                                         then (e00', (e11,
                                                                                       If (dist (f [b00; b11; e00'; e11])) & (pvchecks (f [b00; b11; e00'; e11]))
                                                                                      then
                                                                                        (If (! (isin pv00 ((pi1 (d 1 fphi02')), ((pi1 (d 2 fphi02')), (pi1 (d 3 fphi02'))))))
                                                                                         then (shufl (pi1 (d 1 fphi02')) (pi1 (d 2 fphi02')) (pi1 (d 3 fphi02'))) else O) else |_), (O,
                                                  (If (IF ((dist fphi02')& (pvchecks fphi02')) then
                                                             (IF (! (isin pv00 ((pi1 (d 1 fphi02')), ((pi1 (d 2 fphi02')), (pi1 (d 3 fphi02'))))))
                                                              then (bnlcheck y (nonce 21) (f [b00; b11; e00'; e11; (shufl (pi1 (d 1 fphi02')) (pi1 (d 2 fphi02')) (pi1 (d 3 fphi02')))]))
                                                              else (bnlcheck y (nonce 21) (f [b00; b11; e00'; e11; O])))
                                                       else (bnlcheck y (nonce 21) (f [b00; b11; e00'; e11; |_]))) then
                                                     (enc ( If (dist (f [b00; b11; e00'; e11])) & (pvchecks (f [b00; b11; e00'; e11]))
                                                                                      then
                                                                                        (If (! (isin pv00 ((pi1 (d 1 fphi02')), ((pi1 (d 2 fphi02')), (pi1 (d 3 fphi02')))))) then  (label y (f [b00; b11; e00'; e11; (shufl (pi1 (d 1 fphi02')) (pi1 (d 2 fphi02')) (pi1 (d 3 fphi02')))])) else (label y (f [b00; b11; e00'; e11; O]))) else (label y (f [b00; b11; e00'; e11; |_])), (k1, THREE)) (pke 11) (er 10)) else O, |_))) else |_)]) in ch. *)
 simpl in ch.
      Focus 4. constructor.
repeat constructor. simpl.

       Focus 4.

       apply ch. repeat try split; simpl; try apply vchecksImplyVoteEql. auto.

Qed.


