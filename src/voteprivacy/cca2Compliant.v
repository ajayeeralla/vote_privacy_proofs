Require Export contextCompHid.
Import ListNotations.

Module cca2Compliant.

Definition CxtOneVarMsg: Type := message -> message.

Definition CxtOneVarBol: Type:= message -> Bool.

Definition CxtListOneVar: Type:= message -> list message.

(* This definition is actually the cca2compliant definition given in the ACM paper *)
Inductive IsContextCCA2Msg (n: nat): CxtOneVarMsg -> Prop:=
(* | CGround (t: message) (H: closMsg t = true) (H1: message_beq t (nonce n) = false): IsContextCCA2Msg n (fun _ => t) *)
| CO: IsContextCCA2Msg _ (fun _ => O)
| Cnonce (n1: nat): IsContextCCA2Msg _ (fun _ => nonce n1)
| rewDec C1 C2 (H1: IsContextCCA2Msg n C1) (H2: IsContextCCA2Msg n C2): IsContextCCA2Msg n (fun (x: message) => If ((C1 x) #? x) then (C2 x) else (dec (C1 x) (ske n)))
| Cifm_then_else_ C1 C2 C3 (H1: IsContextCCA2Bol n C1) (H2: IsContextCCA2Msg n C2) (H3: IsContextCCA2Msg n C3):
  IsContextCCA2Msg n (fun (x: message) => ifm_then_else_ (C1 x) (C2 x) (C3 x))
| Cpair C1 C2 (H1: IsContextCCA2Msg n C1) (H2: IsContextCCA2Msg n C2): IsContextCCA2Msg n (fun (x: message) => pair (C1 x) (C2 x))
| Cpi1 C1 (H1: IsContextCCA2Msg n C1): IsContextCCA2Msg n (fun (x: message) => pi1 (C1 x))
| Cpi2 C1 (H1: IsContextCCA2Msg n C1): IsContextCCA2Msg n (fun (x: message) => pi2 (C1 x))
| Cto C1 (H1: IsContextCCA2Msg n C1): IsContextCCA2Msg n (fun (x: message) => to (C1 x))
| CL C1 (H1: IsContextCCA2Msg n C1): IsContextCCA2Msg n (fun (x: message) => L (C1 x))
| Cf L (H1: IsContextCCA2ListMsg n L): IsContextCCA2Msg n (fun (x: message) => f (L x))             
| CONE: IsContextCCA2Msg n (fun _ => ONE)
| CTWO: IsContextCCA2Msg n (fun _ => TWO)
| CTHREE: IsContextCCA2Msg n (fun _ => THREE)
| CA: IsContextCCA2Msg n (fun _ => A)
| CB: IsContextCCA2Msg n (fun _ => B)
| CM: IsContextCCA2Msg n (fun _ => M)
| CC1: IsContextCCA2Msg n (fun _ => C1)
| CC2: IsContextCCA2Msg n (fun _ => C2)
| CC3: IsContextCCA2Msg n (fun _ => C3)
| CV0 C1 (H1: IsContextCCA2Msg n C1): IsContextCCA2Msg n (fun (x: message) => V0 (C1 x))
| CV1 C1 (H1: IsContextCCA2Msg n C1): IsContextCCA2Msg n (fun (x: message) => V1 (C1 x))
| Cpubkey C1 (H1: IsContextCCA2Msg n C1): IsContextCCA2Msg n (fun (x: message) => pubkey (C1 x))
(* Commitments *)
| Ckc C1 (H1: IsContextCCA2Msg n C1): IsContextCCA2Msg n (fun (x: message) => kc (C1 x))
| Ccomm C1 C2 (H1: IsContextCCA2Msg n C1) (H2: IsContextCCA2Msg n C2):
  IsContextCCA2Msg n (fun (x: message) => comm (C1 x) (C2 x))
| Copen C1 C2 C3 (H1: IsContextCCA2Msg n C1) (H2: IsContextCCA2Msg n C2) (H3: IsContextCCA2Msg n C3):
  IsContextCCA2Msg n (fun (x: message) => open (C1 x) (C2 x) (C3 x))
(* shuffling *)
| Cshufle C1 C2 C3 (H1: IsContextCCA2Msg n C1) (H2: IsContextCCA2Msg n C2) (H3: IsContextCCA2Msg n C3):
  IsContextCCA2Msg n (fun (x: message) => shufl (C1 x) (C2 x) (C3 x))
(* Encryptions  *)
| Cke C1 (H1: IsContextCCA2Msg n C1): IsContextCCA2Msg n (fun (x: message) => ke (C1 x))
| Cre C1 (H1: IsContextCCA2Msg n C1): IsContextCCA2Msg n (fun (x: message) => re (C1 x))
| Cenc C1 C2 C3 (H1: IsContextCCA2Msg n C1) (H2: IsContextCCA2Msg n C2) (H3: IsContextCCA2Msg n C3):
  IsContextCCA2Msg n (fun (x: message) => enc (C1 x) (C2 x) (C3 x))
(* | Cdec C1 C2 (H1: IsContextCCA2Msg n C1) (H2: IsContextCCA2Msg n C2): *)
(*   IsContextCCA2Msg n (fun (x: message) => dec (C1 x) (C2 x)) *)
(* Blind signatures *)
| Cbot : IsContextCCA2Msg n (fun _ => bot)
| Ckb C1 (H1: IsContextCCA2Msg n C1): IsContextCCA2Msg n (fun (x: message) => kb (C1 x))
| Crb C1 (H1: IsContextCCA2Msg n C1): IsContextCCA2Msg n (fun (x: message) => rb (C1 x))
| Cbsign C1 C2 C3 (H1: IsContextCCA2Msg n C1) (H2: IsContextCCA2Msg n C2) (H3: IsContextCCA2Msg n C3):
  IsContextCCA2Msg n (fun (x: message) => bsign (C1 x) (C2 x) (C3 x))
| Cbl C1 C2 C3 (H1: IsContextCCA2Msg n C1) (H2: IsContextCCA2Msg n C2) (H3: IsContextCCA2Msg n C3):
  IsContextCCA2Msg n (fun (x: message) => bl (C1 x) (C2 x) (C3 x))
| Cub C1 C2 C3 C4 (H1: IsContextCCA2Msg n C1) (H2: IsContextCCA2Msg n C2) (H3: IsContextCCA2Msg n C3) (H4: IsContextCCA2Msg n C4):
  IsContextCCA2Msg n (fun (x: message) => ub (C1 x) (C2 x) (C3 x) (C4 x))
(* Signatures *)
| Cks C1 (H1: IsContextCCA2Msg n C1): IsContextCCA2Msg n (fun (x: message) => ks (C1 x))
| Crs C1 (H1: IsContextCCA2Msg n C1): IsContextCCA2Msg n (fun (x: message) => rs (C1 x))
| Csign C1 C2 C3 (H1: IsContextCCA2Msg n C1) (H2: IsContextCCA2Msg n C2) (H3: IsContextCCA2Msg n C3):
  IsContextCCA2Msg n (fun (x: message) => sign (C1 x) (C2 x) (C3 x))
(* Zero symbol  *)
| Cz C1 (H1: IsContextCCA2Msg n C1): IsContextCCA2Msg n (fun (x: message) => z (C1 x))
(* Compl symbol *)
| Ccompl C1 (H1: IsContextCCA2Msg n C1): IsContextCCA2Msg n (fun (x: message) => compl (C1 x))
| CVar: IsContextCCA2Msg n (fun (x: message) => x)
with
  IsContextCCA2Bol (n: nat): CxtOneVarBol -> Prop :=
| CTRue: IsContextCCA2Bol n (fun (x: message) => TRue)
| CFAlse: IsContextCCA2Bol n (fun (x: message) => FAlse)
| Ceqb C1 C2 (H1: IsContextCCA2Bol n C1) (H2: IsContextCCA2Bol n C2): IsContextCCA2Bol n (fun (x: message) => eqb (C1 x) (C2 x))
| Ceqm C1 C2 (H1: IsContextCCA2Msg n C1) (H2: IsContextCCA2Msg n C2): IsContextCCA2Bol n (fun (x: message) => eqm (C1 x) (C2 x))
| Cifb_then_else_ C1 C2 C3 (H1: IsContextCCA2Bol n C1) (H2: IsContextCCA2Bol n C2) (H3: IsContextCCA2Bol n C3):
  IsContextCCA2Bol n (fun (x: message) => ifb_then_else_ (C1 x) (C2 x) (C3 x))         
| Cacc C1 C2 C3 C4 (H1: IsContextCCA2Msg n C1) (H2: IsContextCCA2Msg n C2) (H3: IsContextCCA2Msg n C3) (H4: IsContextCCA2Msg n C4):
  IsContextCCA2Bol n (fun (x: message) => acc (C1 x) (C2 x) (C3 x) (C4 x))
| Cbver C1 C2 C3 (H1: IsContextCCA2Msg n C1) (H2: IsContextCCA2Msg n C2) (H3: IsContextCCA2Msg n C3):
  IsContextCCA2Bol n (fun (x: message) => bver (C1 x) (C2 x) (C3 x))
| Cver C1 C2 C3 (H1: IsContextCCA2Msg n C1) (H2: IsContextCCA2Msg n C2) (H3: IsContextCCA2Msg n C3):
  IsContextCCA2Bol n (fun (x: message) => ver (C1 x) (C2 x) (C3 x)) 
with
  IsContextCCA2ListMsg (n: nat): CxtListOneVar -> Prop:=
| CNil: IsContextCCA2ListMsg n (fun _ => [ ])
| CCons C L (H1:IsContextCCA2Msg n C) (H2:IsContextCCA2ListMsg n L): IsContextCCA2ListMsg n (fun (x :message) => (C x)::(L x)).


(* Axiom contextCpa: forall n n1 n2 {f: message -> message}, IsContextCCA2Msg n n f -> [msg (f ({u}_n^^n1))] ~ [msg (f ({u'}_n^^n2))]. *)

Definition CxtOneVarOs := message -> oursum.
Check CxtOneVarOs.
Inductive IsContextCCA2Os (n: nat): CxtOneVarOs -> Prop :=
  | CMsg C (H: IsContextCCA2Msg n C): IsContextCCA2Os n (fun (x: message) => msg (C x))
  | CBol C (H: IsContextCCA2Bol n C): IsContextCCA2Os n (fun (x: message) => bol (C x)).

Definition CxtOslistOneVar := message -> oslist.
Check CxtOslistOneVar.  
Inductive IsContextCCA2Oslist (n: nat): CxtOslistOneVar -> Prop :=
| Cnil: IsContextCCA2Oslist n (fun _ => [ ])
| Ccons C L (H1:IsContextCCA2Os n C) (H2:IsContextCCA2Oslist n L): IsContextCCA2Oslist n (fun (x :message) => (C x)::(L x)). 
(* Definition CxtMylist (n: nat) := message -> mylist n. *)
(* Inductive IsContextMylist (n1 n2: nat) (u u': message): CxtMylist n1 -> Prop := *)
(*   | Cnil: IsContextMylist 0 _ u u' (fun _ => []). *)
(* Check CxtMylist. *)
(* Inductive IsContextMylist {n}: CxtMylist n -> Prop :=. *)
  

(* Axiom CxtListCxtMylist: forall {n} (l: mylist n), IsContextListMsg (fun (x: message) => (toListm l)) -> IsContextMylist  (fun (x: message) => l). *)
                              
Definition Test: CxtOneVarMsg:=  (fun (x: message) => pair (V0 x) x).
Definition Test1: CxtOneVarMsg:=  (fun (x: message) => dec x (ske 3)).
Definition TestList: CxtListOneVar := (fun (x: message) => (cons x nil)).

Lemma TestContext: IsContextCCA2Msg 3 Test.
Proof. repeat constructor. Qed.

Lemma TestListContext: IsContextCCA2ListMsg 3 TestList.
Proof. repeat constructor.
Qed.

Definition contextPhi1:= (fun (x: message) => let v0 := V0 (f (toListm phi0)) in
      let v1 := V1 (f (toListm phi0)) in
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
      (* let t0 := (((vk 0), (Mvar 5), sign (Mvar 5) (ssk 0) (sr 14)), ((vk 1), (Mvar 6), sign (Mvar 6) (ssk 1) (sr 15))) in *)
      (* let t1 := (t0, f (cons t0 nil)) in *)
      let t2 := (((vk 0), b00, sign b00 (ssk 0) (sr 14)), ((vk 1), b11, sign b11 (ssk 1) (sr 15))) in
      let t3 := (t2, f (cons t2 nil)) in
      (* let t2 := ({{ 5 := b00 }} ({{ 6:= b11 }} t0)) in *)
      (* let t3  := ({{ 5 := b00 }} ({{ 6:= b11 }} t1)) in *)
      let acc00 := (acc c00 t r0 t2) in
      let acc11 := (acc c11 t r1 t3) in
      let pv00 := (c00, ((ub c00 t r0 t2), (nonce 20))) in
      let pv11 := (c11, ((ub c11 t r1 t3), (nonce 21))) in
      let e00 := x in
      let e11 := (enc (pv11, TWO) (pke 11) (er 8)) in
      let phi02:= [msg b00, msg b11, msg e00, msg e11] in
      let fphi02:= f (toListm phi02) in
      let s0 := (If (! (isin pv00 ((pi1 (d 1 fphi02)), ((pi1 (d 2 fphi02)), (pi1 (d 3 fphi02))))))
                 then (shufl (pi1 (d 1 fphi02)) (pi1 (d 2 fphi02)) (pi1 (d 3 fphi02))) else O)in
      let dv0 := (If (dist fphi02) & (pvchecks fphi02) then s0 else |_) in
      let phi03:= phi02 ++[msg dv0] in
      let fphi03 := f (toListm phi03) in
      fphi03).
                                                                                                            (*let l00 := (If (bnlcheck c00 (nonce 20) fphi03)
                  then (enc ((label c00 fphi03), (k0, THREE)) (pke 11) (er 9)) else O) in
      let l11 := (If (bnlcheck c11 (nonce 21) fphi03)
                  then (enc ((label c11 fphi03), (k1, THREE)) (pke 11) (er 10)) else O) in
      let phi05:= phi03++[msg l00, msg l11] in
      let fphi05 := f (toListm phi05) in
      let do0 := (If (dist fphi05) & (pochecks fphi05) & ((isink k0 fphi05) & (isink k1 fphi05)) (*or (! ((isink k0 fphi05)or (isink k1 fphi05))))*)
                  then (sotrm fphi05) else |_) in
      let t0s0 := (If acc00 & acc11 then ((e00, (e11, dv0)), (l00, (l11, do0))) else |_) in
      f (toListm [msg b00, msg b11, msg t0s0])).
                                                                                                             *)
 
Lemma TestContextPhi1: IsContextCCA2Msg 11 contextPhi1. 
Proof. repeat constructor. unfold not. 
Admitted.

End cca2Compliant.
