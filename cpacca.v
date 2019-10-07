Require Export prop1.
Eval compute in eqb FAlse FAlse.
Eval compute in eqm O O.
(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                     Rohit Chadha <chadhar@missouri.edu>              *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)

(** * Formalization of the section12 in the paper *)

(** Auxiliary functions  *) 
 
(** Check if (rs n) occurs, and returns TRUE if (rs n) occurs, FALSE otherwise *)
(** It is enough to check if n occurs instead *)
 Fixpoint  checkrsnbol (n:nat) (t:Bool) : bool :=
 match t with 
| eqb  b1 b2 =>  (orb (checkrsnbol n b1)  (checkrsnbol n b2))
| eqm t1 t2 => orb (checkrsnmsg n t1) (checkrsnmsg n t2)
| ifb_then_else_ t1 t2 t3 => orb (checkrsnbol n t1)(orb (checkrsnbol n t2)(checkrsnbol n t3))
| bver t1 t2 t3 => (orb  (orb (checkrsnmsg n t1) (checkrsnmsg n t2)) (checkrsnmsg n t3))
| ver t1 t2 t3 => (orb  (orb (checkrsnmsg n t1) (checkrsnmsg n t2)) (checkrsnmsg n t3))
| acc t1 t2 t3  t4 => (orb (orb  (orb (checkrsnmsg n t1) (checkrsnmsg n t2)) (checkrsnmsg n t3))  (checkrsnmsg n t4))
| _ => false
 end
with checkrsnmsg (n:nat) (t:message) : bool :=
       orb (message_beq (r n) t)
           match t with
             | N n' =>  (beq_nat n' n)
             | ifm_then_else_ b3 t1 t2 => (orb (checkrsnbol n b3) (orb (checkrsnmsg n  t1)(checkrsnmsg n t2)))
             | pair t1 t2 => (orb (checkrsnmsg n t1) (checkrsnmsg n t2))
             | L t1 => (checkrsnmsg n t1)
             | pi1 t1 => (checkrsnmsg n t1)
             | pi2 t1 =>  (checkrsnmsg n t1)
             | to t1 => (checkrsnmsg n t1)
             | f l => (@existsb message (checkrsnmsg n) l)
             (** Vote Values *)                
             | V0 t1 => (checkrsnmsg n t1)
             | V1 t1 => (checkrsnmsg n t1)
             (** public key *)
             | pubkey t1 => (checkrsnmsg n t1)
             (* commitments *)
             | kc t1 => (checkrsnmsg n t1)
             | comm t1 t2 => (orb (checkrsnmsg n t1) (checkrsnmsg n t2))     
             | open t1 t2 t3 =>  orb (checkrsnmsg n t1) (orb (checkrsnmsg n t2) (checkrsnmsg n t3))
             (* shuffling *)
             | shufl t1 t2 t3 =>  orb (checkrsnmsg n t1) (orb (checkrsnmsg n t2) (checkrsnmsg n t3))
             (* Encryptions *)
             | re t1 =>  (checkrsnmsg n t1)
             | ke t1 =>  (checkrsnmsg n t1)
             | enc t1 t2 t3 =>  orb (checkrsnmsg n t1) (orb (checkrsnmsg n t2) (checkrsnmsg n t3))
             | dec t1 t2 => orb (checkrsnmsg n t1) (checkrsnmsg n t2)
             (* Blind Signatues *)
             | kb t1 => (checkrsnmsg n t1)
             | rb t1 => (checkrsnmsg n t1)
             | bsign t1 t2 t3 =>  orb (checkrsnmsg n t1) (orb (checkrsnmsg n t2) (checkrsnmsg n t3))
             | bl t1 t2 t3 =>  orb (checkrsnmsg n t1) (orb (checkrsnmsg n t2) (checkrsnmsg n t3))
             | ub t1 t2 t3  t4 => (orb (orb  (orb (checkrsnmsg n t1) (checkrsnmsg n t2)) (checkrsnmsg n t3))  (checkrsnmsg n t4))
             (* Signatures *)
             | ks t1 => (checkrsnmsg n t1)
             | rs t1 => (checkrsnmsg n t1)
             | sign t1 t2 t3 => (orb (checkrsnmsg n t1) (orb (checkrsnmsg n t2) (checkrsnmsg n t3)))  
             | _ => false
           end.
 

(** Check if (r n) occurs in oursum *)

Definition checkrsnos (n:nat)(t:oursum): bool :=
  match t with 
    |bol b => checkrsnbol n b
    |msg t =>checkrsnmsg n t
  end.

(* Check if (r n) occurs in mylist m, for some m *)

Fixpoint checkrsnmylis {m:nat}(x:nat) (ml :  mylist m):bool :=
  match ml with
    | [] => false
    | h : ml1 => (orb (checkrsnos x h) (checkrsnmylis x ml1))
  end.

(** Check if (sk n) occurs *)

(** Check in terms of type message and Bool  *)

 Fixpoint checksknbol (n:nat) (t:Bool) : bool :=
 match t with 
| eqb  b1 b2 =>  (orb (checksknbol n b1)  (checksknbol n b2))
| eqm t1 t2 => orb (checksknmsg n t1) (checksknmsg n t2)
| ifb_then_else_ t1 t2 t3 => orb (checksknbol n t1)(orb (checksknbol n t2)(checksknbol n t3))
| bver t1 t2 t3 => (orb  (orb (checksknmsg n t1) (checksknmsg n t2)) (checksknmsg n t3))
| ver t1 t2 t3 => (orb  (orb (checksknmsg n t1) (checksknmsg n t2)) (checksknmsg n t3))
| acc t1 t2 t3  t4 => (orb (orb  (orb (checksknmsg n t1) (checksknmsg n t2)) (checksknmsg n t3))  (checksknmsg n t4))
| _ => false
 end
with checksknmsg (n:nat) (t:message) : bool :=
       orb (message_beq (r n) t)
           match t with
             | N n' =>  (beq_nat n' n)
             | ifm_then_else_ b3 t1 t2 => (orb (checksknbol n b3) (orb (checksknmsg n  t1)(checksknmsg n t2)))
             | pair t1 t2 => (orb (checksknmsg n t1) (checksknmsg n t2))
             | L t1 => (checksknmsg n t1)
             | pi1 t1 => (checksknmsg n t1)
             | pi2 t1 =>  (checksknmsg n t1)
             | to t1 => (checksknmsg n t1)
             | f l => (@existsb message (checksknmsg n) l)
             (** Vote Values *)                
             | V0 t1 => (checksknmsg n t1)
             | V1 t1 => (checksknmsg n t1)
             (** public key *)
             | pubkey t1 => (checksknmsg n t1)
             (* commitments *)
             | kc t1 => (checksknmsg n t1)
             | comm t1 t2 => (orb (checksknmsg n t1) (checksknmsg n t2))     
             | open t1 t2 t3 =>  orb (checksknmsg n t1) (orb (checksknmsg n t2) (checksknmsg n t3))
             (* shuffling *)
             | shufl t1 t2 t3 =>  orb (checksknmsg n t1) (orb (checksknmsg n t2) (checksknmsg n t3))
             (* Encryptions *)
             | re t1 =>  (checksknmsg n t1)
             | ke t1 =>  (checksknmsg n t1)
             | enc t1 t2 t3 =>  orb (checksknmsg n t1) (orb (checksknmsg n t2) (checksknmsg n t3))
             | dec t1 t2 => orb (checksknmsg n t1) (checksknmsg n t2)
             (* Blind Signatues *)
             | kb t1 => (checksknmsg n t1)
             | rb t1 => (checksknmsg n t1)
             | bsign t1 t2 t3 =>  orb (checksknmsg n t1) (orb (checksknmsg n t2) (checksknmsg n t3))
             | bl t1 t2 t3 =>  orb (checksknmsg n t1) (orb (checksknmsg n t2) (checksknmsg n t3))
             | ub t1 t2 t3  t4 => (orb (orb  (orb (checksknmsg n t1) (checksknmsg n t2)) (checksknmsg n t3))  (checksknmsg n t4))
             (* Signatures *)
             | ks t1 => (checksknmsg n t1)
             | rs t1 => (checksknmsg n t1)
             | sign t1 t2 t3 => (orb (checksknmsg n t1) (orb (checksknmsg n t2) (checksknmsg n t3)))  
             | _ => false
           end.

 

Eval compute in checksknmsg 1 (pi1 (pi2(kc (N 1)))  ).


(** Check if (sk n) occurs in term of type oursum *)

Definition checksknos (n:nat)(t:oursum): bool :=
  match t with 
    |bol b =>checksknbol n b 
    |msg t =>checksknmsg n t
  end.

(** Check if (sk n) occurs in term of type mylist m for some m *)

Fixpoint checksknmylis {m:nat}(x:nat) (ml :  mylist m):bool :=
  match ml with
    | [] => true
    | h : ml1 => (orb (checksknos x h) (checksknmylis x ml1))
  end.

(** list free variables in a term *)
 (*
Section mvars.
Variable f: message -> list nat.
Fixpoint mapmvars_msg (l: list message) : list nat :=
  match l with
    | nil => nil
    | cons h t => (app (f h) (mapmvars_msg t))
  end.
End mvars.
Fixpoint mvars_bol (t: Bool) : list nat :=
  match t with 
    | eqb  b1 b2 =>  (app (mvars_bol b1) (mvars_bol b2) )
    | eqm t1 t2 => (app (mvars_msg t1) (mvars_msg t2) )
    | ifb t1 t2 t3 => (app (mvars_bol t1) (app (mvars_bol t2) (mvars_bol t3)))
    | EQL t1 t2 => (app (mvars_msg t1) (mvars_msg t2) )
    | ver t1 t2 t3 => (app (mvars_msg t1) (app (mvars_msg t2) (mvars_msg t3)))
    | _ => nil
 end
with mvars_msg (t:message) : list nat :=
       match t with 
         | ifm b3 t1 t2 => (app (mvars_bol b3) (app (mvars_msg t1) (mvars_msg t2))) 
         | (Mvar n') => (cons n' nil)
         | exp t1 t2 t3 => (app (mvars_msg t1) (app (mvars_msg t2) (mvars_msg t3)))
         | pair t1 t2 =>  (app (mvars_msg  t1) (mvars_msg t2) )
         | pi1 t1 => (mvars_msg t1) 
         | pi2 t1 => (mvars_msg t1)
         | ggen t1 =>  (mvars_msg t1)
         | act t1 =>  (mvars_msg t1)
         | rr t1 =>  (mvars_msg t1) 
         | rs t1 =>  (mvars_msg t1) 
         | L t1 =>  (mvars_msg t1) 
         | m t1 =>  (mvars_msg t1) 
         | enc t1 t2 t3 => (app (mvars_msg t1) (app (mvars_msg t2) (mvars_msg t3)))
         | dec t1 t2 =>  (app (mvars_msg t1) (mvars_msg t2))
         | k t1 =>  (mvars_msg t1) 
         | to t1 =>  (mvars_msg t1) 
         | reveal t1 =>  (mvars_msg t1) 
         | sign t1 t2 =>   (app (mvars_msg t1) (mvars_msg t2))
         | f l =>  (@mapmvars_msg mvars_msg l)
         | _ => nil
       end.
 
(** list free variables in a term of type oursum *)

Definition mvars_os (t:oursum) :list nat :=
  match t with
    | msg t1 => mvars_msg t1
    | bol b1 => mvars_bol b1
  end.
(** list free variables in a term of type mylist *)

Fixpoint mvars_mylis {n} (l:mylist n) : list nat :=
  match l with
    | [] => nil
    | h :: t => app (mvars_os h) (mvars_mylis t)
  end. 



(** Computation of a list without duplication *)
Fixpoint nodup (l:list nat) : list nat :=
  match l with
    | nil => nil
    | cons h t => if (leb 1 (@count_occ nat eq_nat_dec t h) ) then (nodup t) else (cons h (nodup t))
  end.
Eval compute in nodup [2;2;4;4;5].*)
(** * Axioms *)


Eval compute in {O}_1^^2.
(** Equational theory for asymmetric encryption scheme *)

Axiom dep_enc :  forall(n:nat) (x z :message), (dec (enc x (pke n) z) (ske n)) # x.

(*Definition distvars {n} (l :mylist n) := nodup (mvars_mylis  l).*)

Notation "'[' x '<-' s ']' l" :=  (submsg_mylist x s l).

(** ENCCPA assumption *) 
 
Axiom ENCCPA: forall (u u' u'': message) (n n1 n2 n3 :nat) {m} (l:mylist m), (leb (length (distMvars l)) 1) = true /\ (closMlist [u; u'; u''] = true) /\ ((checkrsnmylis n2 l) = false) /\ ((checkrsnmylis n3 l) = false)/\ ((checkrsnmylis n1 l) = false)  -> 
 ([ n <- (If (|u|#?|u'|) then {u}_n1^^n2 else u'')] l) ~ ([ n <-  (If (|u|#?|u'|) then {u'}_n1^^n3 else u'')] l).


(** ENCCCA1 assumption *) 

Axiom ENCCCA1 : forall (t u u' u'': message) (n n1 n2 n3 :nat){m} (l :mylist m), (leb (length (distMvars l)) 1) = true /\ (closMlist [u; u'; u''] = true) /\ ((checkrsnmylis n2 l) = false) /\ ((checkrsnmylis n3 l) = false)/\ (checkmtmylis t l) = true /\ (mVarMsg t = (cons n nil)) -> (checkmtmylis (dec t (ske n1)) l) = false ->
  ([ n <- (If (|u|#?|u'|) then {u}_n1^^n2 else u'')] l) ~ ([ n <-  (If (|u|#?|u'|) then {u'}_n1^^n3 else u'')] l).

(** To check if a term t is [(n1 u u')] compliant *)

Section compliant.
  Variable f: message -> bool.
   Fixpoint aplycca2comp  (l:list message) :bool :=
    match l with
      | nil => true 
      | cons h t => (andb (f h) (aplycca2comp t))
    end.                   
End compliant.


Fixpoint cca2compmsg (t' t'':message) (n n1:nat) (u u':message) (t:message) :bool :=
(negb (checkmtmsg (ske n) t)) ||  match t with 
      | N n' => true
      | ifm_then_else_ b1 t4 t5 => if (message_beq t (If (t'#? (Mvar n)) & (eqm (L u) (L u')) then t'' else (dec t' (ske n1)))) then true
                        else (andb (cca2compbol t' t'' n n1 u u' b1) (andb (cca2compmsg t' t'' n n1 u u' t4) (cca2compmsg t' t'' n n1 u u' t5)))
      | pair t1 t2 => (andb (cca2compmsg t' t'' n n1 u u' t1) (cca2compmsg t' t'' n n1 u u' t2))
      | pi2 t1 =>  (cca2compmsg t' t'' n n1 u u' t1)
      | to t1 => (cca2compmsg t' t'' n n1 u u' t1)
      | pi1 t1 => (cca2compmsg t' t'' n n1 u u' t1)
      | f l => (aplycca2comp (cca2compmsg t' t'' n n1 u u') l)
      (* Vote values *)
      | V0 t1 => (cca2compmsg t' t'' n n1 u u' t1)
      | V1 t1 => (cca2compmsg t' t'' n n1 u u' t1)
      (* public key *)
      | pubkey t1 => (cca2compmsg t' t'' n n1 u u' t1)
      (** commitments *)
      | kc t1 => true
      | comm t1 t2 => (andb (cca2compmsg t' t'' n n1 u u' t1) (cca2compmsg t' t'' n n1 u u' t2))
      | open t1 t2 t3 => (andb (cca2compmsg t' t'' n n1 u u' t1) (andb (cca2compmsg t' t'' n n1 u u' t2) (cca2compmsg t' t'' n n1 u u' t3)))
      (** encryptions *)
      | ke t1 => true
      | re t1 => true 
      | enc t1 t2 t3 => (andb (cca2compmsg t' t'' n n1 u u' t1) (andb (cca2compmsg t' t'' n n1 u u' t2) (cca2compmsg t' t'' n n1 u u' t3)))
      | dec t1  t2 => if (andb (leb 1 (@count_occ nat eq_nat_dec (mVarMsg t1) n)) (message_beq (ske n1) t2)) then false else (andb (cca2compmsg t' t'' n n1 u u' t1) (cca2compmsg t' t'' n n1 u u' t2))   
      (** Blind digital signatures *)
      | kb t1 => true
      | rb t1 => true                                                                                                 
      | bl t1 t2 t3 => (andb (cca2compmsg t' t'' n n1 u u' t1) (andb (cca2compmsg t' t'' n n1 u u' t2) (cca2compmsg t' t'' n n1 u u' t3)))
      | ub t1 t2 t3 t4 => (andb (andb (cca2compmsg t' t'' n n1 u u' t1) (andb (cca2compmsg t' t'' n n1 u u' t2) (cca2compmsg t' t'' n n1 u u' t3))) (cca2compmsg t' t'' n n1 u u' t4))
      | bsign t1 t2 t3 => (andb (cca2compmsg t' t'' n n1 u u' t1) (andb (cca2compmsg t' t'' n n1 u u' t2) (cca2compmsg t' t'' n n1 u u' t3)))
      (** signatures *)
      | ks t1 => true
      | rs t1 => true                                                            
      | sign t1 t2 t3 => (andb (cca2compmsg t' t'' n n1 u u' t1) (andb (cca2compmsg t' t'' n n1 u u' t2) (cca2compmsg t' t'' n n1 u u' t3)))
       (* shuffling *)
      | shufl t1 t2 t3 => (andb (cca2compmsg t' t'' n n1 u u' t1) (andb (cca2compmsg t' t'' n n1 u u' t2) (cca2compmsg t' t'' n n1 u u' t3)))
      | _ => true
               
  end
with cca2compbol t' t'' (n n1:nat) (u u':message)  (b:Bool) :bool :=
       match b with 
         | eqb b1 b2 => (andb (cca2compbol t' t'' n n1 u u' b1) (cca2compbol t' t''  n n1 u u' b2))
         | eqm  t1 t2 =>  (andb (cca2compmsg t' t'' n n1 u u' t1) (cca2compmsg t' t''  n n1 u u' t2))
         | ifb_then_else_  b1 b2 b3 =>  (andb (cca2compbol t' t'' n n1 u u' b1) (andb (cca2compbol t' t'' n n1 u u' b2) (cca2compbol t' t'' n n1 u u' b3)))
         | ver  t1 t2 t3 => (andb (cca2compmsg t' t'' n n1 u u' t1) (andb (cca2compmsg t' t'' n n1 u u' t2) (cca2compmsg t' t'' n n1 u u' t3)))
         | bver  t1 t2 t3 => (andb (cca2compmsg t' t'' n n1 u u' t1) (andb (cca2compmsg t' t'' n n1 u u' t2) (cca2compmsg t' t'' n n1 u u' t3)))
         | acc t1 t2 t3 t4 => (andb (andb (cca2compmsg t' t'' n n1 u u' t1) (andb (cca2compmsg t' t'' n n1 u u' t2) (cca2compmsg t' t'' n n1 u u' t3))) (cca2compmsg t' t'' n n1 u u' t4))
         | _ => true
       end.
  
Definition cca2compos (t' t'':message) (n n1:nat) ( u u' :message) (t:oursum) : bool :=
  match t with
    | msg s => cca2compmsg t' t'' n n1 u u' s
    | bol b => cca2compbol t' t'' n n1 u u' b
  end.
Fixpoint cca2compmylis (t' t'':message) (n n1:nat) (u u':message) {m} (l:mylist m):bool :=
  match l with
    | [] => true
    | h : t => if (cca2compos t' t'' n n1 u u' h) then (cca2compmylis t' t'' n n1 u u' t) else false
  end.                                                                                
(** ENCCCA2 assumption *)



Axiom ENCCCA2 : forall (t' t'' u u' u'': message) (n n1 n2 n3 :nat){m} (l :mylist m), (leb (length (distMvars ([msg t' , msg t''] ++ l))) 1) = true /\ (closMlist [u; u'; u''] = true) /\ (cca2compmylis t' t'' n n1 u u' l) = true /\ ( (cca2compmsg t' t'' n n1 u u' t') = true) /\ (cca2compmsg t' t'' n n1 u u' t'') = true ->
                                                                                                             ([ n <- (If (|u|#?|u'|) then {u}_n1^^n2 else u'')] l) ~ ([ n <-  (If (|u|#?|u'|) then {u'}_n1^^n3 else u'')] l).

(** Extended ENCCCA2 *)

Axiom tempax: forall t n n' n1 u u' v v', (dec t (ske n1)) # (If (t#? (Mvar n)) & (|u|#?|u'|) then (dec (Mvar n) (ske n1)) else
                                                                (If (t#?(Mvar n'))& (|v|#?|v'|) then (dec (Mvar n') (ske n1)) else (dec t (ske n1)))).

(** To check if a term t is [(n1 u u')] compliant *)

Section extCompliant.
  Variable f: message -> bool.
   Fixpoint aplyExtcca2comp  (l:list message) :bool :=
    match l with
      | nil => true 
      | cons h t => (andb (f h) (aplyExtcca2comp t))
    end.                   
End extCompliant.


Fixpoint extCca2compmsg (t':message) (n n' n1:nat) (u u' v v':message) (t:message) :bool :=
    match t with 
      | Mvar n2 => (beq_nat n2 n) || (beq_nat n2 n')
      | N n2 => (negb (beq_nat n2 n1))
      | ifm_then_else_ b1 t4 t5 => (extCca2compbol t' n n' n1 u u' v v' b1)
                                     (** if (message_beq t (If (t'#? (Mvar n)) & (|u|#?|u'|) then (dec (Mvar n) (ske n1)) else
                                                                (If (t'#?(Mvar n'))& (|v|#?|v'|) then (dec (Mvar n') (ske n1)) else (dec t' (ske n1))))) then true
                        else (andb (extCca2compbol t' n n' n1 u u' v v' b1) (andb (extCca2compmsg t' n n' n1 u u' v v' t4) (extCca2compmsg t' n n' n1 u u' v v' t5))) *)
      | pair t1 t2 => (andb (extCca2compmsg t' n n' n1 u u' v v' t1) (extCca2compmsg t' n n' n1 u u' v v' t2))
      | pi2 t1 =>  (extCca2compmsg t' n n' n1 u u' v v' t1)
      | to t1 => (extCca2compmsg t' n n' n1 u u' v v' t1)
      | pi1 t1 => true
      | f l => (aplycca2comp (extCca2compmsg t' n n' n1 u u' v v') l)
      (* Vote values *)
      | V0 t1 => (extCca2compmsg t' n n' n1 u u' v v' t1)
      | V1 t1 => (extCca2compmsg t' n n' n1 u u' v v' t1)
      (* public key *)
      | pubkey t1 => (extCca2compmsg t' n n' n1 u u' v v' t1)
      (** commitments *)
      | kc t1 => (extCca2compmsg t' n n' n1 u u' v v' t1)
      | comm t1 t2 => (andb (extCca2compmsg t' n n' n1 u u' v v' t1) (extCca2compmsg t' n n' n1 u u' v v' t2))
      | open t1 t2 t3 => (andb (extCca2compmsg t' n n' n1 u u' v v' t1) (andb (extCca2compmsg t' n n' n1 u u' v v' t2) (extCca2compmsg t' n n' n1 u u' v v' t3)))
      (** encryptions *)
      | ke t1 => (extCca2compmsg t' n n' n1 u u' v v' t1)
      | re t1 => (extCca2compmsg t' n n' n1 u u' v v' t1)   
      | enc t1 t2 t3 => (andb (extCca2compmsg t' n n' n1 u u' v v' t1) (andb (extCca2compmsg t' n n' n1 u u' v v' t2) (extCca2compmsg t' n n' n1 u u' v v' t3)))
      | dec t1  t2 => true (*if (andb (leb 2 (@count_occ nat eq_nat_dec (mVarMsg t1) n)) (message_beq (ske n1) t2)) then false else (andb (extCca2compmsg t' n n' n1 u u' v v' t1) (extCca2compmsg t' n n' n1 u u' v v' t2)) *)  
      (** Blind digital signatures *)
      | kb t1 => (extCca2compmsg t' n n' n1 u u' v v' t1)
      | rb t1 => (extCca2compmsg t' n n' n1 u u' v v' t1)                                                                                                    
      | bl t1 t2 t3 => (andb (extCca2compmsg t' n n' n1 u u' v v' t1) (andb (extCca2compmsg t' n n' n1 u u' v v' t2) (extCca2compmsg t' n n' n1 u u' v v' t3)))
      | ub t1 t2 t3 t4 => (andb (andb (extCca2compmsg t' n n' n1 u u' v v' t1) (andb (extCca2compmsg t' n n' n1 u u' v v' t2) (extCca2compmsg t' n n' n1 u u' v v' t3))) (extCca2compmsg t' n n' n1 u u' v v' t4))
      | bsign t1 t2 t3 => (andb (extCca2compmsg t' n n' n1 u u' v v' t1) (andb (extCca2compmsg t' n n' n1 u u' v v' t2) (extCca2compmsg t' n n' n1 u u' v v' t3)))
      (** signatures *)
      | ks t1 => (extCca2compmsg t' n n' n1 u u' v v' t1)
      | rs t1 => (extCca2compmsg t' n n' n1 u u' v v' t1)                                                            
      | sign t1 t2 t3 => (andb (extCca2compmsg t' n n' n1 u u' v v' t1) (andb (extCca2compmsg t' n n' n1 u u' v v' t2) (extCca2compmsg t' n n' n1 u u' v v' t3)))
       (* shuffling *)
      | shufl t1 t2 t3 => (andb (extCca2compmsg t' n n' n1 u u' v v' t1) (andb (extCca2compmsg t' n n' n1 u u' v v' t2) (extCca2compmsg t' n n' n1 u u' v v' t3)))
      | _ => true
               
  end
with extCca2compbol t' (n n' n1:nat) (u u' v v':message)  (b:Bool) :bool :=
       match b with 
         | eqb b1 b2 => (andb (extCca2compbol t' n n' n1 u u' v v' b1) (extCca2compbol t' n n' n1 u u' v v' b2))
         | eqm  t1 t2 =>  (andb (extCca2compmsg t' n n' n1 u u' v v' t1) (extCca2compmsg t' n n' n1 u u' v v' t2))
         | ifb_then_else_  b1 b2 b3 =>  (andb (extCca2compbol t' n n' n1 u u' v v' b1) (andb (extCca2compbol t' n n' n1 u u' v v' b2) (extCca2compbol t' n n' n1 u u' v v' b3)))
         | ver  t1 t2 t3 => (andb (extCca2compmsg t' n n' n1 u u' v v' t1) (andb (extCca2compmsg t' n n' n1 u u' v v' t2) (extCca2compmsg t' n n' n1 u u' v v' t3)))
         | bver  t1 t2 t3 => (andb (extCca2compmsg t' n n' n1 u u' v v' t1) (andb (extCca2compmsg t' n n' n1 u u' v v' t2) (extCca2compmsg t' n n' n1 u u' v v' t3)))
         | acc t1 t2 t3 t4 => (andb (andb (extCca2compmsg t' n n' n1 u u' v v' t1) (andb (extCca2compmsg t' n n' n1 u u' v v' t2) (extCca2compmsg t' n n' n1 u u' v v' t3))) (extCca2compmsg t' n n' n1 u u' v v' t4))
         | _ => true
       end.
  
Definition extCca2compos (t':message) (n n' n1:nat) (u u' v v' :message) (t:oursum) : bool :=
  match t with
    | msg s => extCca2compmsg t' n n' n1 u u' v v' s
    | bol b => extCca2compbol t' n n' n1 u u' v v' b
  end.
Fixpoint extCca2compmylis (t':message) (n n' n1:nat) (u u' v v':message) {m} (l:mylist m):bool :=
  match l with
    | [] => true
    | h : t => if (extCca2compos t' n n' n1 u u' v v' h) then (extCca2compmylis t' n n' n1 u u' v v' t) else false
  end.                                                                                
(** EXTENCCCA2 assumption *)

Axiom EXTENCCCA2 : forall (t' u u' u'' v v' v'': message) (n n' n1 n2 n3 n4 n5:nat){m} (l:mylist m), ( (length (distMvars ([msg t'] ++ l))) <=? 2) = true /\ (closMlist [u; u'; u''] = true) /\ (closMlist [v; v'; v''] = true) /\ (extCca2compmylis t' n n' n1 u u' v v' l) = true /\ ((extCca2compmsg t' n n' n1 u u' v v' t') = true) -> 
  ([n' <- (If (|v|#?|v'|) then {v}_n1^^n3 else v'')][ n <- (If (|u|#?|u'|) then {u}_n1^^n2 else u'')] l) ~ ([n' <- (If (|v|#?|v'|) then {v'}_n1^^n5 else v'')][ n <-  (If (|u|#?|u'|) then {u'}_n1^^n4 else u'')] l).

 


(** * Example 12.2 *)
(*
(** nonce and key generation *)

Axiom ln: forall n, lnc # (L (N n)).

(** Definition lskey {n} := (L (sk n))*)

(** length regular *)

Axiom len_regular: forall (x1 x2 y1 y2 :message), (L x1) # (L y1) /\ (L x2) # (L y2) -> (L (pair x1 x2)) # (L (pair y1 y2)).

(** Idempotence: L(L(x)) = L(x) *)

Axiom idemp_L: forall x,  (L (L x)) # (L x).

Axiom lskey: forall n, lsk # (L (sk n)). *)

(** few tactics *)
   Ltac tryrewhyps :=
   match goal with
     | [|- context [beq_nat ?n1 ?n2] ] =>  match goal with
                                            | [H: beq_nat n2 n1 = ?Y |- _ ] => rewrite <- Nat.eqb_sym in H; try rewrite H; try split; try reflexivity
                                            | [H1: beq_nat n1 n2 = ?Y1 |- _] => rewrite H1; try split; try reflexivity
                                          end
   end. 
   
(* Ltac beqneq n1 n2 :=
 assert( n1 <> n2) ; simpl; try omega;
                                       match goal with
                                         | [H : ?X <> ?Y |- _ ] => try rewrite <-beq_nat_false_iff in H 
                                       end . *)
 (*
Theorem ex122: forall n, 
 [ msg (enc (pair (sk (n+2)) (N (n+6))) (pk (n+3)) (rs (N ((n+4))))); msg (enc (pair (pi2 (dec (f [ (enc (pair (sk (n+2)) (N (n+6))) (pk (n+3)) (rs (N ((n+4)))))]) (sk (n+3)))) (N n)) (pk (n+2)) (rs (N (n+5)))); msg (N n)] ~
 [ msg (enc (pair (sk  (n+2)) (N (n+6))) (pk (n+3)) (rs (N ((n+4))))); msg (enc (pair (pi2 (dec (f [ (enc (pair (sk (n+2)) (N (n+6))) (pk (n+3)) (rs (N ((n+4)))))]) (sk (n+3)))) (N n)) (pk (n+2)) (rs (N (n+5)))); msg (N (n+1))].


Proof. intros .
(******************************************************************************************)
assert(tfx: (f [ (enc (pair (sk (n+2)) (N (n+6))) (pk (n+3)) (rs (N ((n+4)))))]) # (ifm (eqm (f [ (enc (pair (sk (n+2)) (N (n+6))) (pk (n+3)) (rs (N ((n+4)))))])  (enc (pair (sk (n+2)) (N (n+6))) (pk (n+3)) (rs (N ((n+4)))))) (f [ (enc (pair (sk (n+2)) (N (n+6))) (pk (n+3)) (rs (N ((n+4)))))]) (f [ (enc (pair (sk (n+2)) (N (n+6))) (pk (n+3)) (rs (N ((n+4)))))]))).

rewrite IFSAME_M with (b:=  (eqm (f [ (enc (pair (sk (n+2)) (N (n+6))) (pk (n+3)) (rs (N ((n+4)))))])  (enc (pair (sk (n+2)) (N (n+6))) (pk (n+3)) (rs (N ((n+4))))))) (x:= (f [ (enc (pair (sk (n+2)) (N (n+6))) (pk (n+3)) (rs (N ((n+4)))))])). 
reflexivity.

assert (tdecfx:  (pi2 (dec (f [ (enc (pair (sk (n+2)) (N (n+6))) (pk (n+3)) (rs (N ((n+4)))))]) (sk (n+3)))) # (ifm  (eqm (f [ (enc (pair (sk (n+2)) (N (n+6))) (pk (n+3)) (rs (N ((n+4)))))])  (enc (pair (sk (n+2)) (N (n+6))) (pk (n+3)) (rs (N ((n+4)))))) (N (n+6))  (pi2 (dec (f [ (enc (pair (sk (n+2)) (N (n+6))) (pk (n+3)) (rs (N ((n+4)))))]) (sk (n+3)))))).

rewrite tfx at 1. 

pose proof(Example11_M).
apply  Forall_ELM_EVAL_M1 with (n:=1) (x :=  (f [enc (pair (sk (n+2)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))])) in H; simpl in H.
apply  Forall_ELM_EVAL_M1 with (n:=2) (x := (enc (pair (sk (n+2)) ( N (n+6) )) (pk (n+3)) (rs (N (n+4)))) ) in H; simpl in H.
apply  Forall_ELM_EVAL_M1 with (n:=3) (x :=  (f [enc (pair (sk (n+2)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))])) in H; simpl in H.
 rewrite H .
assert(H3:  (pi2 (dec (ifm (Bvar 0)  (Mvar 1)  (Mvar 2)) (sk (n+3)))) # (ifm (Bvar 0) (pi2 (dec (Mvar 1) (sk (n+3)))) (pi2 (dec (Mvar 2) (sk (n+3)))))).
rewrite <- IFSAME_M with (b:= (Bvar 0)) (x:=  (pi2 (dec (ifm (Bvar 0)  (Mvar 1)  (Mvar 2)) (sk (n+3))))).
rewrite IFEVAL_M .
simpl.
rewrite IFTRUE_M.
rewrite IFFALSE_M.
reflexivity.
apply Forall_ELM_EVAL_M with (n:=0) (x:= (eqm (f [enc (pair (sk (n+2)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (enc (pair (pi2 (k (N (n+2)))) (N (n+6))) (pi1 (k (N (n+3)))) (rs (N (n+4)))))) in H3.
simpl in H3.
apply  Forall_ELM_EVAL_M1 with (n:=1) (x :=  (enc (pair (pi2 (k (N (n+2)))) (N (n+6))) (pi1 (k (N (n+3)))) (rs (N (n+4))))) in H3. simpl in H3.
apply  Forall_ELM_EVAL_M1 with (n:=2) (x := (f [enc (pair (sk (n+2))  (N (n+6))) (pk (n+3)) (rs (N (n+4)))])) in H3. simpl in H3.
rewrite H3.
pose proof(dep_enc).
rewrite dep_enc with (n:=(n+3)) (x:=  (pair (pi2 (k (N (n+2)))) (N (n+6) ))) .
rewrite proj2 with (m1:= (pi2 (k (N (n+2))))) (m2 := (N (n+6))) .
reflexivity.

(************************************************************************************************)
assert(ufx: (f [ (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N ((n+4)))))]) # (ifm (eqm (f [ (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N ((n+4)))))])  (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N ((n+4)))))) (f [ (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N ((n+4)))))]) (f [ (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N ((n+4)))))]))).
pose proof (IFSAME_M).
rewrite IFSAME_M with (b:=  (eqm (f [ (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N ((n+4)))))])  (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N ((n+4))))))) (x:= (f [ (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N ((n+4)))))])). 
reflexivity.
assert (udecfx:  (pi2 (dec (f [ (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N ((n+4)))))]) (sk (n+3)))) # (ifm  (eqm (f [ (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N ((n+4)))))])  (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N ((n+4)))))) (N (n+6))  (pi2 (dec (f [ (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N ((n+4)))))]) (sk (n+3)))))).
rewrite ufx at 1.
pose proof(Example11_M) as H0.
apply  Forall_ELM_EVAL_M1 with (n:=1) (x :=  (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))])) in H0. simpl in H0.
apply  Forall_ELM_EVAL_M1 with (n:=2) (x := (enc (pair (sk (n+7)) ( N (n+6) )) (pk (n+3)) (rs (N (n+4)))) ) in H0. simpl in H0.
apply  Forall_ELM_EVAL_M1 with (n:=3) (x :=  (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))])) in H0. simpl in H0.
rewrite H0 .
assert(Hf3:  (pi2 (dec (ifm (Bvar 0)  (Mvar 1)  (Mvar 2)) (sk (n+3)))) # (ifm (Bvar 0) (pi2 (dec (Mvar 1) (sk (n+3)))) (pi2 (dec (Mvar 2) (sk (n+3)))))).
rewrite <- IFSAME_M with (b:= (Bvar 0)) (x:=  (pi2 (dec (ifm (Bvar 0)  (Mvar 1)  (Mvar 2)) (sk (n+3))))).
rewrite IFEVAL_M .
simpl.
rewrite IFTRUE_M.
rewrite IFFALSE_M.
reflexivity.
apply Forall_ELM_EVAL_M with (n:=0) (x:= (eqm (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (enc (pair (pi2 (k (N (n+7)))) (N (n+6))) (pi1 (k (N (n+3)))) (rs (N (n+4)))))) in Hf3.
simpl in Hf3.
apply  Forall_ELM_EVAL_M1 with (n:=1) (x :=  (enc (pair (pi2 (k (N (n+7)))) (N (n+6))) (pi1 (k (N (n+3)))) (rs (N (n+4))))) in Hf3. simpl in Hf3.
apply  Forall_ELM_EVAL_M1 with (n:=2) (x := (f [enc (pair (sk (n+7))  (N (n+6))) (pk (n+3)) (rs (N (n+4)))])) in Hf3. simpl in Hf3.

rewrite Hf3.
pose proof(dep_enc).
rewrite dep_enc with (n:=(n+3)) (x:=  (pair (pi2 (k (N (n+7)))) (N (n+6) ))) .
rewrite proj2 with (m1:= (pi2 (k (N (n+7))))) (m2 := (N (n+6))) .
reflexivity.

(*L<sk1 , (n+6)> , L<sk6, (n+6)> *)

assert(H2: (L (pair (sk (n+2)) (N (n+6)))) # (L (pair (sk (n+7)) (N (n+6))))).

apply len_regular.  split.
Focus 2.
reflexivity.

assert(H3: lsk # ( L (sk (n+2)))).
rewrite lskey with (n:= (n+2)).

reflexivity.

assert(H4: lsk # ( L (sk (n+7)))).
rewrite lskey with (n:= (n+7)).

reflexivity.

rewrite <- H3.
rewrite <- H4.
reflexivity.
apply EQmsg in H2.

pose proof (IFTRUE_M  (enc (pair (sk (n+2)) (N (n+6))) (pk (n+3)) (rs (N ((n+4))))) O).
rewrite <- H2 in H.

pose proof (IFTRUE_M  (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N ((n+4))))) O).
rewrite <- H2 in H0.

simpl.
(*************************************************************************************************)
(*************************************************************************************************)


assert(TT: ( submsg_mylist 1   (ifm (eqm (L (pair (sk (n+2)) (N (n+6)))) (L (pair (sk (n+7)) (N (n+6)))))
          (enc (pair (sk (n+2)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))) O) [msg (Mvar 1); msg (enc (pair (ifm (eqm (f [Mvar 1]) (Mvar 1)) (N (n+6)) (pi2 (dec (f [Mvar 1]) (sk (n+3))))) (N n))  (pk (n+2)) (rs (N (n+5)))) ; msg (N n)]) ~ (submsg_mylist 1  (ifm (eqm (L (pair (sk (n+2)) (N (n+6)))) (L (pair (sk (n+7)) (N (n+6)))))
           (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))) O) [msg (Mvar 1); msg (enc (pair (ifm (eqm (f [Mvar 1]) (Mvar 1)) (N (n+6)) (pi2 (dec (f [Mvar 1]) (sk (n+3))))) (N n))  (pk (n+2)) (rs (N (n+5)))) ; msg (N n)])).
  
assert((eqm (L (pair (sk (n+2)) (N (n+6)))) (L (pair (sk (n+7)) (N (n+6))))) ## TRue).
assert(  (L (pair (sk (n+2)) (N (n+6)))) # (L (pair (sk (n+7)) (N (n+6))))).
apply len_regular. split.
rewrite <- lskey with (n:= (n+2)).
rewrite <- lskey. reflexivity.
reflexivity.
rewrite EQmsg in H1. assumption.
assert ( (ifm
                 (eqm (f [Mvar 1]) (Mvar 1)) &
                 (eqm (L (pair (sk (n+2)) (N (n+6)))) (L (pair (sk (n+7)) (N (n+6)))))
                 (N (n+6)) (pi2 (dec (f [Mvar 1]) (sk (n+3))))) #  (ifm
                 (eqm (f [Mvar 1]) (Mvar 1)) 
                 (N (n+6)) (pi2 (dec (f [Mvar 1]) (sk (n+3)))))).
rewrite H1.
unfold andB.
rewrite IFTFb. reflexivity.
rewrite <- H3.
apply ENCCCA2 with (n:=1)  (t'':= (N (n+6))) (g:=pi2) (t':=  (f [Mvar 1])) (u:= (pair (sk (n+2)) (N (n+6)))) (u':= (pair (sk (n+7)) (N (n+6)))) (u'':= O) (n1 := (n+3)) (n2 :=(n+4)) (n3:= (n+4))  (l:=  [msg (Mvar 1);
      msg
        (enc
           (pair
              (ifm
                 (eqm (f [Mvar 1]) (Mvar 1)) &
                 (eqm (L (pair (sk (n+2)) (N (n+6)))) (L (pair (sk (n+7)) (N (n+6)))))
                 (N (n+6)) (pi2 (dec (f [Mvar 1]) (sk (n+3))))) 
              (N n)) (pk (n+2)) (rs (N (n+5)))); msg (N n)]);  try split;try reflexivity.
try split;repeat reflexivity. split. simpl.
repeat rewrite <- beq_nat_refl. simpl. 
beqneq (n+2) (n+3).
beqneq (n+2) (n+3).
beqneq (n+5) (n+3).
beqneq n (n+3).
repeat tryrewhyps; try split;simpl; try reflexivity. try split ; simpl; try reflexivity.
beqneq (n+6) (n+3); tryrewhyps.

assert(UU: ( submsg_mylist 1   (ifm (eqm (L (pair (sk (n+2)) (N (n+6)))) (L (pair (sk (n+7)) (N (n+6)))))
          (enc (pair (sk (n+2)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))) O)   [msg (Mvar 1); msg (enc (pair (ifm (eqm (f [Mvar 1]) (Mvar 1)) (N (n+6)) (pi2 (dec (f [Mvar 1]) (sk (n+3))))) (N n))  (pk (n+2)) (rs (N (n+5)))) ; msg (N (n+1))]) ~ (submsg_mylist 1  (ifm (eqm (L (pair (sk (n+2)) (N (n+6)))) (L (pair (sk (n+7)) (N (n+6)))))
                                                                                                                                                                                                                                              (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))) O)   [msg (Mvar 1); msg (enc (pair (ifm (eqm (f [Mvar 1]) (Mvar 1)) (N (n+6)) (pi2 (dec (f [Mvar 1]) (sk (n+3))))) (N n))  (pk (n+2)) (rs (N (n+5))))  ; msg (N (n+1))])).

assert((eqm (L (pair (sk (n+2)) (N (n+6)))) (L (pair (sk (n+7)) (N (n+6))))) ## TRue).
assert(  (L (pair (sk (n+2)) (N (n+6)))) # (L (pair (sk (n+7)) (N (n+6))))).
apply len_regular. split.
rewrite <- lskey with (n:= (n+2)).
rewrite <- lskey. reflexivity.
reflexivity.
rewrite EQmsg in H1. assumption.

assert ( (ifm
                 (eqm (f [Mvar 1]) (Mvar 1)) &
                 (eqm (L (pair (sk (n+2)) (N (n+6)))) (L (pair (sk (n+7)) (N (n+6)))))
                 (N (n+6)) (pi2 (dec (f [Mvar 1]) (sk (n+3))))) #  (ifm
                 (eqm (f [Mvar 1]) (Mvar 1)) 
                 (N (n+6)) (pi2 (dec (f [Mvar 1]) (sk (n+3)))))).
rewrite H1.
unfold andB.
rewrite IFTFb. reflexivity.
rewrite <- H3.


apply ENCCCA2 with (n:=1) (g:=pi2) (t'':= (N (n+6))) (t':= f[ Mvar 1]) (u:= (pair (sk (n+2)) (N (n+6)))) (u':= (pair (sk (n+7)) (N (n+6)))) (u'':= O) (n1 := (n+3)) (n2 :=(n+4)) (n3:= (n+4))  (l:=   [msg (Mvar 1); msg (enc (pair  (ifm
                 (eqm (f [Mvar 1]) (Mvar 1)) &
                 (eqm (L (pair (sk (n+2)) (N (n+6)))) (L (pair (sk (n+7)) (N (n+6)))))
                 (N (n+6)) (pi2 (dec (f [Mvar 1]) (sk (n+3)))))  (N n))  (pk (n+2)) (rs (N (n+5)))) ; msg (N (n+1))]).
simpl. 
repeat (try split; try reflexivity);  repeat rewrite <- beq_nat_refl;  simpl.
beqneq n (n+3); beqneq (n+2) (n+3);  beqneq (n+5) (n+3) ;  beqneq (n+1) (n+3); repeat tryrewhyps; simpl; try reflexivity.

 beqneq (n+6) (n+3) ;repeat tryrewhyps; simpl; try reflexivity.
rewrite H in TT.
rewrite H0 in TT.
simpl in TT.
rewrite <- tdecfx in TT.
rewrite <- udecfx  in TT.

(*Assumption on lengths*)

assert(HT: (L (pair (pi2 (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N n))) # (L (pair (pi2 (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N (n+8))))).
apply len_regular.
split. reflexivity.
assert(t1 : lnc # ( L (N n))).
rewrite ln with (n:=n).
reflexivity.
rewrite <- t1.
rewrite ln with (n:= (n+8)).
reflexivity.
rewrite EQmsg in HT.

assert(TTT: ( submsg_mylist 1 (ifm (eqm (L (pair (pi2 (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N n)))  (L (pair (pi2 (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N (n+8))))) (enc (pair (pi2 (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N n)) (pk (n+2)) (rs (N (n+5)))) O)   [msg (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))); msg (Mvar 1) ; msg (N n)]) ~ (submsg_mylist 1 (ifm (eqm (L (pair (pi2 (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N n)))  (L (pair (pi2 (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N (n+8))))) (enc (pair (pi2 (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N (n+8))) (pk (n+2)) (rs (N (n+5)))) O) [msg (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))); msg (Mvar 1) ; msg (N n)])).
  
apply ENCCCA2 with (n:=1) (g:=pi2) (t'' := (Mvar 1)) (t':= (Mvar 1)) (u:= (pair (pi2 (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N n))) (u':=  (pair (pi2 (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N (n+8)))) (u'':= O) (n1 := (n+2)) (n2 :=(n+5)) (n3:= (n+5))  (l:=  [msg (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))); msg (Mvar 1) ; msg (N n)]). 

assert( cca2compmylis pi2 (Mvar 1) (Mvar 1) 1 (n+2)
     (pair
        (pi2
           (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3))))
        (N n))
     (pair
        (pi2
           (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3))))
        (N (n+8)))
     [msg (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))); 
       msg (Mvar 1); msg (N n)] = true ).
unfold cca2compmylis.
assert(cca2compos pi2 (Mvar 1) (Mvar 1) 1 (n+2)
         (pair
            (pi2
               (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))])
                  (sk (n+3)))) (N n))
         (pair
            (pi2
               (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))])
                  (sk (n+3)))) (N (n+8)))
         (msg (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4))))) = true).  
simpl.
   
  beqneq (n + 7 ) (n + 2);beqneq (n+6) (n+2);  beqneq (n+3) (n+2) ;  beqneq (n+4) (n+2); repeat tryrewhyps; simpl; try reflexivity.  simpl.
 beqneq (n + 7 ) (n + 2);beqneq (n+6) (n+2);  beqneq (n+3) (n+2) ;  beqneq (n+4) (n+2); beqneq n (n+2); repeat tryrewhyps; simpl; try split; try reflexivity. 
simpl; try split;  try reflexivity; 
  beqneq (n + 7 ) (n + 2);beqneq (n+6) (n+2);  beqneq (n+3) (n+2) ;  beqneq (n+4) (n+2); beqneq n (n+2); repeat tryrewhyps; simpl; try split; try reflexivity. 
assert( cca2compos pi2 (Mvar 1) (Mvar 1) 1 (n+2)
          (pair
             (pi2
                (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))])
                   (sk (n+3)))) (N n))
          (pair
             (pi2
                (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))])
                   (sk (n+3)))) (N (n+8))) (msg (Mvar 1)) = true).
reflexivity.

rewrite HT in TTT.
repeat rewrite IFTRUE_M in TTT.
simpl in TTT.
assert(t1t6n7: [msg (enc (pair (sk (n+2)) (N (n+6))) (pk (n+3)) (rs (N (n+4))));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk (n+2)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N n)) (pk (n+2)) (rs (N (n+5)))); msg (N n)] ~  [msg (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4))));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N (n+8))) (pk (n+2)) (rs (N (n+5)))); msg (N n)]).
apply EQI_trans with (ml2:= [msg (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4))));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N n)) (pk (n+2)) (rs (N (n+5)))); msg (N n)]).
assumption.

assumption.
rewrite H in UU.
rewrite H0 in UU.
simpl in UU.
rewrite <- udecfx in UU.
rewrite <- tdecfx in UU.

assert(UUU: ( submsg_mylist 1 (ifm (eqm (L (pair (pi2 (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N n)))  (L (pair (pi2 (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N (n+8))))) (enc (pair (pi2 (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N n)) (pk (n+2)) (rs (N (n+5)))) O)   [msg (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))); msg (Mvar 1) ; msg (N (n+1))]) ~ (submsg_mylist 1 (ifm (eqm (L (pair (pi2 (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N n)))  (L (pair (pi2 (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N (n+8))))) (enc (pair (pi2 (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N (n+8))) (pk (n+2)) (rs (N (n+5)))) O) [msg (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))); msg (Mvar 1) ; msg (N (n+1))])).

apply ENCCCA2 with (n:=1) (g:= pi2)  (t'':= (Mvar 1)) (t':= (Mvar 1)) (u:= (pair (pi2 (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N n))) (u':=  (pair (pi2 (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N (n+8)))) (u'':= O) (n1 := (n+2)) (n2:=(n+5)) (n3:= (n+5))  (l:=  [msg (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))); msg (Mvar 1) ; msg (N (n+1))]);simpl; try split; try reflexivity.
try split; try reflexivity.

beqneq (n + 7 ) (n + 2);beqneq (n+6) (n+2);  beqneq (n+3) (n+2) ;  beqneq (n+4) (n+2);  beqneq (n+1) (n+2);  repeat tryrewhyps; simpl; try split; try reflexivity. 

      
rewrite HT in UUU.
repeat rewrite IFTRUE_M in UUU.
simpl in UUU.
assert(u1u6n7: [msg (enc (pair (sk (n+2)) (N (n+6))) (pk (n+3)) (rs (N (n+4))));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk (n+2)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N n)) (pk (n+2)) (rs (N (n+5)))); msg (N (n+1))] ~  [msg (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4))));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N (n+8))) (pk (n+2)) (rs (N (n+5)))); msg (N (n+1))]).
apply EQI_trans with (ml2:= [msg (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4))));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N n)) (pk (n+2)) (rs (N (n+5)))); msg (N (n+1))]).
assumption.
assumption.
assert(Final :  [msg (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4))));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N (n+8))) (pk (n+2)) (rs (N (n+5)))); msg (N n)] ~  [msg (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4))));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N (n+8))) (pk (n+2)) (rs (N (n+5)))); msg (N (n+1))]).

pose proof( FRESHIND_rs 2 n (n+1)   [msg (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4))));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N (n+8))) (pk (n+2)) (rs (N (n+5))))]  [msg (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4))));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N (n+8))) (pk (n+2)) (rs (N (n+5))))]).
simpl in H3.

beqneq (n + 8) n ; beqneq (n + 7) n ; beqneq (n + 6) n ;beqneq (n + 5) n; beqneq (n + 4) n; beqneq (n + 3) n; beqneq (n + 2) n; beqneq (n + 1) n;
beqneq (n + 8) (n + 1) ;beqneq (n + 7) (n + 1) ; beqneq (n + 6) (n + 1) ;beqneq (n + 5) (n + 1) ; beqneq (n + 4) (n + 1) ; beqneq (n + 3) (n+1); beqneq (n + 2) (n + 1).
assert ((if beq_nat (n + 7) n then false else true) &&
       (if beq_nat (n + 6) n then false else true) &&
       ((if beq_nat (n + 3) n then false else true) &&
        (if beq_nat (n + 4) n then false else true)) &&
       ((if beq_nat (n + 7) n then false else true) &&
        (if beq_nat (n + 6) n then false else true) &&
        ((if beq_nat (n + 3) n then false else true) &&
         (if beq_nat (n + 4) n then false else true)) && true &&
        (if beq_nat (n + 3) n then false else true) &&
        (if beq_nat (n + 8) n then false else true) &&
        ((if beq_nat (n + 2) n then false else true) &&
         (if beq_nat (n + 5) n then false else true)) &&
        ((if beq_nat (n + 7) n then false else true) &&
         (if beq_nat (n + 6) n then false else true) &&
         ((if beq_nat (n + 3) n then false else true) &&
          (if beq_nat (n + 4) n then false else true)) &&
         ((if beq_nat (n + 7) n then false else true) &&
          (if beq_nat (n + 6) n then false else true) &&
          ((if beq_nat (n + 3) n then false else true) &&
           (if beq_nat (n + 4) n then false else true)) && true &&
          (if beq_nat (n + 3) n then false else true) &&
          (if beq_nat (n + 8) n then false else true) &&
          ((if beq_nat (n + 2) n then false else true) &&
           (if beq_nat (n + 5) n then false else true)) && true))) = true).
repeat tryrewhyps. repeat rewrite H19 in H3; clear H19.

 assert ((if beq_nat (n + 7) (n + 1) then false else true) &&
       (if beq_nat (n + 6) (n + 1) then false else true) &&
       ((if beq_nat (n + 3) (n + 1) then false else true) &&
        (if beq_nat (n + 4) (n + 1) then false else true)) &&
       ((if beq_nat (n + 7) (n + 1) then false else true) &&
        (if beq_nat (n + 6) (n + 1) then false else true) &&
        ((if beq_nat (n + 3) (n + 1) then false else true) &&
         (if beq_nat (n + 4) (n + 1) then false else true)) && true &&
        (if beq_nat (n + 3) (n + 1) then false else true) &&
        (if beq_nat (n + 8) (n + 1) then false else true) &&
        ((if beq_nat (n + 2) (n + 1) then false else true) &&
         (if beq_nat (n + 5) (n + 1) then false else true)) &&
        ((if beq_nat (n + 7) (n + 1) then false else true) &&
         (if beq_nat (n + 6) (n + 1) then false else true) &&
         ((if beq_nat (n + 3) (n + 1) then false else true) &&
          (if beq_nat (n + 4) (n + 1) then false else true)) &&
         ((if beq_nat (n + 7) (n + 1) then false else true) &&
          (if beq_nat (n + 6) (n + 1) then false else true) &&
          ((if beq_nat (n + 3) (n + 1) then false else true) &&
           (if beq_nat (n + 4) (n + 1) then false else true)) && true &&
          (if beq_nat (n + 3) (n + 1) then false else true) &&
          (if beq_nat (n + 8) (n + 1) then false else true) &&
          ((if beq_nat (n + 2) (n + 1) then false else true) &&
                                                             (if beq_nat (n + 5) (n + 1) then false else true)) && true))) = true).
 repeat tryrewhyps. repeat rewrite H19 in H3; clear H19.

assert( true = true /\ true = true /\ true = true /\ [msg (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4))));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N (n+8))) (pk (n+2)) (rs (N (n+5))))] ~ [msg (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4))));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N (n+8))) (pk (n+2)) (rs (N (n+5))))]). 
repeat (try split; try reflexivity).
apply H3 in H19. apply RESTR_swap with (p1:=1) (p2:=2) in H19. unfold swap_mylist in H19. simpl in H19. apply RESTR_swap with (p1:=2) (p2:=3) in H19. unfold swap_mylist in H19. simpl in H19.
assumption.

assert(result :  [msg (enc (pair (sk (n+2)) (N (n+6))) (pk (n+3)) (rs (N (n+4))));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk (n+2)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N n)) (pk (n+2)) (rs (N (n+5)))); msg (N n)] ~  [msg (enc (pair (sk (n+2)) (N (n+6))) (pk (n+3)) (rs (N (n+4))));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk (n+2)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N n)) (pk (n+2)) (rs (N (n+5)))); msg (N (n+1))]).
apply EQI_trans with (ml2:=  [msg (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4))));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N (n+8))) (pk (n+2)) (rs (N (n+5)))); msg (N n)]).
assumption.
apply EQI_trans with (ml2:=  [msg (enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4))));
        msg
         (enc (pair (pi2 (dec (f [enc (pair (sk (n+7)) (N (n+6))) (pk (n+3)) (rs (N (n+4)))]) (sk (n+3)))) (N (n+8))) (pk (n+2)) (rs (N (n+5)))); msg (N (n+1))]).
assumption. symmetry in u1u6n7. assumption. assumption.
Qed. *)


          