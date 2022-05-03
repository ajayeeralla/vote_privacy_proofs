Require Export contextCompHid.
Import ListNotations.

Module newCca2Compliant.
Search eq.

Inductive Cca2CxtMsg (n n1: nat) (u u': message): message ->  Prop :=
| Cnonce (n2 : nat): beq_nat n n2 = false -> Cca2CxtMsg n n1 u u' (nonce n2)
| CVar n2: n2 = n1 -> Cca2CxtMsg n n1 u u' (Mvar n2) 
| CO: Cca2CxtMsg n n1 u u' O
| Cpair t1 t2 (H1: Cca2CxtMsg n n1 u u' t1) (H2: Cca2CxtMsg n n1 u u' t2): Cca2CxtMsg n n1 u u' (pair t1 t2)
| Cifm_then_else_ b t1 t2 (H1: Cca2CxtBol n n1 u u' b) (H2: Cca2CxtMsg n n1 u u' t1) (H3: Cca2CxtMsg n n1 u u' t2): Cca2CxtMsg n n1 u u' (ifm_then_else_ b t1 t2)
(*| rewDec C1 C2 (H1: Cca2CxtMsg n C1) (H2: Cca2CxtMsg n C2): Cca2CxtMsg n (fun (x: message) => If ((C1 x) #? x) then (C2 x) else (dec (C1 x) (ske n)))*)
| Cpi1 t1 (H1: Cca2CxtMsg n n1 u u' t1): Cca2CxtMsg n n1 u u' t1
| Cpi2 t1 (H1: Cca2CxtMsg n n1 u u' t1): Cca2CxtMsg n n1 u u' t1
| Cto t1 (H1: Cca2CxtMsg n n1 u u' t1): Cca2CxtMsg n n1 u u' t1
| CL t1 (H1: Cca2CxtMsg n n1 u u' t1): Cca2CxtMsg n n1 u u' t1
| Cf L (H1: Cca2CxtListMsg n n1 u u' L): Cca2CxtMsg n n1 u u' (f L) 
| CONE: Cca2CxtMsg n n1 u u' ONE
| CTWO: Cca2CxtMsg n n1 u u' TWO
| CTHREE: Cca2CxtMsg n n1 u u' THREE
| CA: Cca2CxtMsg n n1 u u' A 
| CB: Cca2CxtMsg n n1 u u' B
| CM: Cca2CxtMsg n n1 u u' M
| CC1: Cca2CxtMsg n n1 u u' C1
| CC2: Cca2CxtMsg n n1 u u' C2
| CC3: Cca2CxtMsg n n1 u u' C3
| CV0 C1 (H1: Cca2CxtMsg n n1 u u' C1): Cca2CxtMsg n n1 u u' (V0 C1)
| CV1 C1 (H1: Cca2CxtMsg n n1 u u' C1): Cca2CxtMsg n n1 u u' (V1 C1)
| Cpubkey C1 (H1: Cca2CxtMsg n n1 u u' C1): Cca2CxtMsg n n1 u u' (pubkey C1)
(* Commitments *)
| Ckc C1 (H1: Cca2CxtMsg n n1 u u' C1): Cca2CxtMsg n n1 u u' (kc C1)
| Ccomm C1 C2 (H1: Cca2CxtMsg n n1 u u' C1) (H2: Cca2CxtMsg n n1 u u' C2):
  Cca2CxtMsg n n1 u u' (comm C1 C2)
| Copen C1 C2 C3 (H1: Cca2CxtMsg n n1 u u' C1) (H2: Cca2CxtMsg n n1 u u' C2) (H3: Cca2CxtMsg n n1 u u' C3):
  Cca2CxtMsg n n1 u u' (open C1 C2 C3)
(* shuffling *)
| Cshufle C1 C2 C3 (H1: Cca2CxtMsg n n1 u u' C1) (H2: Cca2CxtMsg n n1 u u' C2) (H3: Cca2CxtMsg n n1 u u' C3):
  Cca2CxtMsg n n1 u u' (shufl C1 C2 C3)
(* Encryptions  *)
| Cke C1 (H1: Cca2CxtMsg n n1 u u' C1): Cca2CxtMsg n n1 u u' (ke C1)
| Cre C1 (H1: Cca2CxtMsg n n1 u u' C1): Cca2CxtMsg n n1 u u' (re C1)
| Cenc C1 C2 C3 (H1: Cca2CxtMsg n n1 u u' C1) (H2: Cca2CxtMsg n n1 u u' C2) (H3: Cca2CxtMsg n n1 u u' C3): Cca2CxtMsg n n1 u u' (enc C1 C2 C3)
| Cdect C1 C2 n2 (H1: Cca2CxtMsg n n1 u u' C1) :  beq_nat n2 n = true  -> Cca2CxtMsg n n1 u u' (If (C1 #? (Mvar n1)) then C2 else (dec C1 (ske n2)))
| Cdecf C1 n2 (H1: Cca2CxtMsg n n1 u u' C1) :  beq_nat n2 n = false  -> Cca2CxtMsg n n1 u u' (dec C1 (ske n2))
(*   Cca2CxtMsg n n1 u u' *)
(* Blind signatures *)
| Cbot : Cca2CxtMsg n n1 u u' bot 
| Ckb C1 (H1: Cca2CxtMsg n n1 u u' C1): Cca2CxtMsg n n1 u u' (kb C1)
| Crb C1 (H1: Cca2CxtMsg n n1 u u' C1): Cca2CxtMsg n n1 u u' (rb C1)
| Cbsign C1 C2 C3 (H1: Cca2CxtMsg n n1 u u' C1) (H2: Cca2CxtMsg n n1 u u' C2) (H3: Cca2CxtMsg n n1 u u' C3): Cca2CxtMsg n n1 u u' (bsign C1 C2 C3)
| Cbl C1 C2 C3 (H1: Cca2CxtMsg n n1 u u' C1) (H2: Cca2CxtMsg n n1 u u' C2) (H3: Cca2CxtMsg n n1 u u' C3): Cca2CxtMsg n n1 u u' (bl C1 C2 C3)
| Cub C1 C2 C3 C4 (H1: Cca2CxtMsg n n1 u u' C1) (H2: Cca2CxtMsg n n1 u u' C2) (H3: Cca2CxtMsg n n1 u u' C3) (H4: Cca2CxtMsg n n1 u u' C4):
  Cca2CxtMsg n n1 u u' (ub C1 C2 C3 C4)
(* Signatures *)
| Cks C1 (H1: Cca2CxtMsg n n1 u u' C1): Cca2CxtMsg n n1 u u' (ks C1)
| Crs C1 (H1: Cca2CxtMsg n n1 u u' C1): Cca2CxtMsg n n1 u u' (rs C1)
| Csign C1 C2 C3 (H1: Cca2CxtMsg n n1 u u' C1) (H2: Cca2CxtMsg n n1 u u' C2) (H3: Cca2CxtMsg n n1 u u' C3): Cca2CxtMsg n n1 u u' (sign C1 C2 C3)
(* Zero symbol  *)
| Cz C1 (H1: Cca2CxtMsg n n1 u u' C1): Cca2CxtMsg n n1 u u' (z C1)
(* Compl symbol *)
| Ccompl C1 (H1: Cca2CxtMsg n n1 u u' C1): Cca2CxtMsg n n1 u u' (compl C1)
with
  Cca2CxtBol (n n1: nat) (u u': message) : Bool -> Prop :=
| CTRue: Cca2CxtBol n n1 u u' TRue
| CFAlse: Cca2CxtBol n n1 u u' FAlse
| Ceqb C1 C2 (H1: Cca2CxtBol n n1 u u' C1) (H2: Cca2CxtBol n n1 u u' C2): Cca2CxtBol n n1 u u' (eqb C1 C2)
| Ceqm C1 C2 (H1: Cca2CxtMsg n n1 u u' C1) (H2: Cca2CxtMsg n n1 u u' C2): Cca2CxtBol n n1 u u' (eqm C1 C2)
| Cifb_then_else_ C1 C2 C3 (H1: Cca2CxtBol n n1 u u' C1) (H2: Cca2CxtBol n n1 u u' C2) (H3: Cca2CxtBol n n1 u u' C3):
  Cca2CxtBol n n1 u u' (ifb_then_else_ C1 C2 C3)         
| Cacc C1 C2 C3 C4 (H1: Cca2CxtMsg n n1 u u' C1) (H2: Cca2CxtMsg n n1 u u' C2) (H3: Cca2CxtMsg n n1 u u' C3) (H4: Cca2CxtMsg n n1 u u' C4):
  Cca2CxtBol n n1 u u' (acc C1 C2 C3 C4)
| Cbver C1 C2 C3 (H1: Cca2CxtMsg n n1 u u' C1) (H2: Cca2CxtMsg n n1 u u' C2) (H3: Cca2CxtMsg n n1 u u' C3):
  Cca2CxtBol n n1 u u' (bver C1 C2 C3)
| Cver C1 C2 C3 (H1: Cca2CxtMsg n n1 u u' C1) (H2: Cca2CxtMsg n n1 u u' C2) (H3: Cca2CxtMsg n n1 u u' C3):
  Cca2CxtBol n n1 u u' (ver C1 C2 C3)
with
  Cca2CxtListMsg (n n1: nat) (u u': message): list message -> Prop:=
| CNil: Cca2CxtListMsg n n1 u u' [ ]
| CCons C L (H1:Cca2CxtMsg n n1 u u' C) (H2:Cca2CxtListMsg n n1 u u' L): Cca2CxtListMsg n n1 u u' (C :: L).
End newCca2Compliant.
Import newCca2Compliant.
Axiom ENCCCA2: forall (n n1 n2 n3: nat) (u u': message) {m} (l: mylist m),
    (|u|#?|u'|) ## TRue ->
    (List.length (distMvars l) <=? 1) = true ->
    distMvars l = (cons n nil) ->
    (closMylist [msg u, msg u'] = true) ->
    Cca2CxtListMsg n1 n u u' (toListm l) ->
    ([ n <- {u}_n1^^n2 ] l) ~ ([ n <- {u'}_n1^^n3] l).
                            
