Require Export auxDefs.
Import ListNotations.

Module Cxt.

Definition CxtTwoVarsMsg: Type:= message -> message -> message.
Definition CxtTwoVarsBol: Type:= message -> message -> Bool.

Definition CxtListTwoVars: Type:= message -> message ->list message.

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


Definition Test : CxtTwoVarsMsg:=  (fun (x: message) (y:message) => pair (V0 x) y).
Definition TestList: CxtListTwoVars := (fun (x: message) (y: message) => [x; y]).
Lemma TestContext: IsContextMsg Test.
Proof. repeat constructor.
Qed.

Lemma TestContextList: IsContextListMsg TestList.
                                    
Proof.
repeat constructor.
Qed.


End Cxt.
