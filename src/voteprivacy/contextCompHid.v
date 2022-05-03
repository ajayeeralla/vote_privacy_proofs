Require Export auxDefs.
Import ListNotations.

Module CxtCompHid.

Definition CxtTwoVarsMsg: Type:= message -> message -> message.
Definition CxtTwoVarsBol: Type:= message -> message -> Bool.

Definition CxtListTwoVars: Type:= message -> message -> list message.


Inductive IsContextMsg: CxtTwoVarsMsg -> Prop:=
| CO: IsContextMsg (fun _ _ => O)
| Cnonce (n: nat): IsContextMsg (fun (x: message) (y: message) => nonce n)
| Cifm_then_else_ C1 C2 C3 (H1: IsContextBol C1) (H2: IsContextMsg C2) (H3: IsContextMsg C3):
  IsContextMsg (fun (x: message) (y: message) => ifm_then_else_ (C1 x y) (C2 x y) (C3 x y))
| Cpair C1 C2 (H1: IsContextMsg C1) (H2: IsContextMsg C2):
  IsContextMsg (fun (x: message) (y: message) => pair (C1 x y) (C2 x y))
| Cpi1 C1 (H1: IsContextMsg C1): IsContextMsg (fun (x: message) (y: message) => pi1 (C1 x y))
| Cpi2 C1 (H1: IsContextMsg C1): IsContextMsg (fun (x: message) (y: message) => pi2 (C1 x y))
| Cto C1 (H1: IsContextMsg C1): IsContextMsg (fun (x: message) (y: message) => to (C1 x y))
| CL C1 (H1: IsContextMsg C1): IsContextMsg (fun (x: message) (y: message) => L (C1 x y))
| Cf L (H1: IsContextListMsg L): IsContextMsg (fun (x: message) (y: message) => f (L x y))             
| CONE: IsContextMsg (fun _ _ => ONE)
| CTWO: IsContextMsg (fun _ _ => TWO)
| CTHREE: IsContextMsg (fun _ _ => THREE)
| CA: IsContextMsg (fun _ _ => A)
| CB: IsContextMsg (fun _ _ => B)
| CM: IsContextMsg (fun _ _ => M)
| CC1: IsContextMsg (fun _ _ => C1)
| CC2: IsContextMsg (fun _ _ => C2)
| CC3: IsContextMsg (fun _ _ => C3)
| CV0 C1 (H1: IsContextMsg C1): IsContextMsg (fun (x: message) (y: message) => V0 (C1 x y))
| CV1 C1 (H1: IsContextMsg C1): IsContextMsg (fun (x: message) (y: message) => V1 (C1 x y))
| Cpubkey C1 (H1: IsContextMsg C1): IsContextMsg (fun (x: message) (y: message) => pubkey (C1 x y))
(* Commitments *)
| Ckc C1 (H1: IsContextMsg C1): IsContextMsg (fun (x: message) (y: message) => kc (C1 x y))
| Ccomm C1 C2 (H1: IsContextMsg C1) (H2: IsContextMsg C2):
  IsContextMsg (fun (x: message) (y: message) => comm (C1 x y) (C2 x y))
| Copen C1 C2 C3 (H1: IsContextMsg C1) (H2: IsContextMsg C2) (H3: IsContextMsg C3):
  IsContextMsg (fun (x: message) (y: message) => open (C1 x y) (C2 x y) (C3 x y))
(* shuffling *)
| Cshufle C1 C2 C3 (H1: IsContextMsg C1) (H2: IsContextMsg C2) (H3: IsContextMsg C3):
  IsContextMsg (fun (x: message) (y: message) => shufl (C1 x y) (C2 x y) (C3 x y))
(* Encryptions  *)
| Cke C1 (H1: IsContextMsg C1): IsContextMsg (fun (x: message) (y: message) => ke (C1 x y))
| Cre C1 (H1: IsContextMsg C1): IsContextMsg (fun (x: message) (y: message) => re (C1 x y))
| Cenc C1 C2 C3 (H1: IsContextMsg C1) (H2: IsContextMsg C2) (H3: IsContextMsg C3):
  IsContextMsg (fun (x: message) (y: message) => enc (C1 x y) (C2 x y) (C3 x y))
| Cdec C1 C2 (H1: IsContextMsg C1) (H2: IsContextMsg C2):
  IsContextMsg (fun (x: message) (y: message) => dec (C1 x y) (C2 x y))
(* Blind signatures *)
| Cbot : IsContextMsg (fun _ _ => bot)
| Ckb C1 (H1: IsContextMsg C1): IsContextMsg (fun (x: message) (y: message) => kb (C1 x y))
| Crb C1 (H1: IsContextMsg C1): IsContextMsg (fun (x: message) (y: message) => rb (C1 x y))
| Cbsign C1 C2 C3 (H1: IsContextMsg C1) (H2: IsContextMsg C2) (H3: IsContextMsg C3):
  IsContextMsg (fun (x: message) (y: message) => bsign (C1 x y) (C2 x y) (C3 x y))
| Cbl C1 C2 C3 (H1: IsContextMsg C1) (H2: IsContextMsg C2) (H3: IsContextMsg C3):
  IsContextMsg (fun (x: message) (y: message) => bl (C1 x y) (C2 x y) (C3 x y))
| Cub C1 C2 C3 C4 (H1: IsContextMsg C1) (H2: IsContextMsg C2) (H3: IsContextMsg C3) (H4: IsContextMsg C4):
  IsContextMsg (fun (x: message) (y: message) => ub (C1 x y) (C2 x y) (C3 x y) (C4 x y))
(* Signatures *)
| Cks C1 (H1: IsContextMsg C1): IsContextMsg (fun (x: message) (y: message) => ks (C1 x y))
| Crs C1 (H1: IsContextMsg C1): IsContextMsg (fun (x: message) (y: message) => rs (C1 x y))
| Csign C1 C2 C3 (H1: IsContextMsg C1) (H2: IsContextMsg C2) (H3: IsContextMsg C3):
  IsContextMsg (fun (x: message) (y: message) => sign (C1 x y) (C2 x y) (C3 x y))
(* Zero symbol  *)
| Cz C1 (H1: IsContextMsg C1): IsContextMsg (fun (x: message) (y: message) => z (C1 x y))
(* Compl symbol *)
| Ccompl C1 (H1: IsContextMsg C1): IsContextMsg (fun (x: message) (y: message) => compl (C1 x y))
| Cproj1: IsContextMsg (fun (x: message) (y: message) => x)
| Cproj2: IsContextMsg (fun (x: message) (y: message) => y)
with
  IsContextBol: CxtTwoVarsBol -> Prop :=
| CTRue: IsContextBol (fun (x: message) (y: message) => TRue)
| CFAlse: IsContextBol (fun (x: message) (y: message) => FAlse)
| Ceqb C1 C2 (H1: IsContextBol C1) (H2: IsContextBol C2): IsContextBol (fun (x: message) (y: message) => eqb (C1 x y) (C2 x y))
| Ceqm C1 C2 (H1: IsContextMsg C1) (H2: IsContextMsg C2): IsContextBol (fun (x: message) (y: message) => eqm (C1 x y) (C2 x y))
| Cifb_then_else_ C1 C2 C3 (H1: IsContextBol C1) (H2: IsContextBol C2) (H3: IsContextBol C3):
  IsContextBol (fun (x: message) (y: message) => ifb_then_else_ (C1 x y) (C2 x y) (C3 x y))         
| Cacc C1 C2 C3 C4 (H1: IsContextMsg C1) (H2: IsContextMsg C2) (H3: IsContextMsg C3) (H4: IsContextMsg C4):
  IsContextBol (fun (x: message) (y: message) => acc (C1 x y) (C2 x y) (C3 x y) (C4 x y))
| Cbver C1 C2 C3 (H1: IsContextMsg C1) (H2: IsContextMsg C2) (H3: IsContextMsg C3):
  IsContextBol (fun (x: message) (y: message) => bver (C1 x y) (C2 x y) (C3 x y))
| Cver C1 C2 C3 (H1: IsContextMsg C1) (H2: IsContextMsg C2) (H3: IsContextMsg C3):
  IsContextBol (fun (x: message) (y: message) => ver (C1 x y) (C2 x y) (C3 x y)) 
with
  IsContextListMsg: CxtListTwoVars -> Prop:=
| CNil: IsContextListMsg (fun (x :message) (y: message)=> [ ])
| CCons C L (H1:IsContextMsg C) (H2:IsContextListMsg L): IsContextListMsg (fun (x :message) (y: message) => (C x y)::(L x y)).

Definition CxtTwoVarsOs := message -> message -> oursum.

Inductive IsContextOs : CxtTwoVarsOs -> Prop :=
  | CMsg C (H: IsContextMsg C): IsContextOs (fun (x: message) (y: message) => msg (C x y))
  | CBol C (H: IsContextBol C): IsContextOs (fun (x: message) (y: message) => bol (C x y)).

Definition CxtOslistTwoVars := message -> message -> oslist.
  
Inductive IsContextOslist: CxtOslistTwoVars -> Prop :=
| Cnil: IsContextOslist (fun (x: message) (y: message) => [ ])
| Ccons C L (H1:IsContextOs C) (H2:IsContextOslist L): IsContextOslist (fun (x :message) (y: message) => (C x y)::(L x y)).

(* Definition CxtMylist (n: nat) : Type := message -> message -> mylist n. *)

(* Inductive IsContextMylist {n}: CxtMylist n -> Prop :=. *)
  

(* Axiom CxtListCxtMylist: forall {n} (l: mylist n), IsContextListMsg (fun (x: message) (y: message) => (toListm l)) -> IsContextMylist  (fun (x: message) (y: message) => l). *)
                              
Definition Test : CxtTwoVarsMsg:=  (fun (x: message) (y:message) => pair (V0 x) y).
Definition TestList: CxtListTwoVars := (fun (x: message) (y: message) => [x; y]).
Lemma TestContext: IsContextMsg Test.
Proof. repeat constructor.
Qed.

Definition contextPhi1:= (fun (x: message) (y: message) => let v0 := V0 (f (toListm phi0)) in
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
      let b00 := (bl x t r0) in
      let b11 := (bl y t r1) in
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
      let e00 := (enc (pv00, TWO) (pke 11) (er 7)) in
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
Lemma TestContextPhi1: IsContextMsg contextPhi1.
Proof. repeat constructor.
Qed.


Lemma TestContextList: IsContextListMsg TestList.                                    
Proof.
repeat constructor.
Qed.


End CxtCompHid.
