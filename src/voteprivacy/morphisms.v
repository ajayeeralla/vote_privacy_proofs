(************************************************************************)
(* Copyright (c) 2017-2018, Ajay Kumar Eeralla <ae266@mail.missouri.edu>*)      
(************************************************************************)
Require Export definitions.

(** This library defines indistinguishability and all morphisms *)
Open Scope msg_scope.


(*Indistinguishability Relation ~*)
(*Definition Ind_Relation := forall n , mylist n -> mylist n -> Prop.*)

(** Indistinguishability relation [EQI]:
[[

forall n, relation (mylist n).
]]

 *)

Parameter EQI : forall {n }, relation (mylist n).

Infix "~" := EQI (at level 0, right associativity): ind_scope.
 Open Scope ind_scope. 
Axiom EQI_equiv: forall n, equiv (mylist n) (@EQI n).

Instance EQI_Equiv :forall n, Equivalence  (@EQI n).
Proof.
split;
repeat apply EQI_equiv.
Qed.  
   
Theorem EQI_ref: forall {n:nat} (ml: mylist n), ml ~ ml.
Proof.
intros m.
apply EQI_equiv.
Qed.

Theorem EQI_sym: forall {n:nat} (ml1 ml2 : mylist n), ml1 ~ ml2 -> ml2 ~ ml1 .
Proof.
intros.
apply EQI_equiv.
assumption.
Qed.

Theorem EQI_trans : forall {n:nat} (ml1 ml2 ml3: mylist n), ml1 ~ ml2 -> ml2 ~ ml3 -> ml1 ~ ml3.
Proof.
  intros.  rewrite <- H in H0; auto.
Qed.

Add Parametric Relation n : (mylist n) (@EQI n)
reflexivity proved by (EQI_ref)
symmetry proved by (EQI_sym)
transitivity proved by (EQI_trans)
as EQI_rel.


(** Equivalence relation [EQm] defined on [message] type.  *)

Definition EQm : relation message := fun (m1:message)  (m2: message) =>  [bol (eqm m1 m2)] ~ [ bol TRue].

Infix "#" := EQm (at level 70, right associativity): ind_scope.


Axiom EQm_equiv: equiv message EQm.

Instance EQm_Equiv : Equivalence  EQm.
Proof.
split;
repeat apply EQm_equiv.
Qed. 

Theorem EQm_ref: forall m:message, m # m.
Proof.
intros m.
apply EQm_equiv.
reflexivity.
Qed.

Theorem EQm_sym: forall m1 m2: message, m1 # m2 -> m2 # m1.
Proof.
intros.
rewrite H.
reflexivity.
Qed.


Theorem EQm_trans : forall m1 m2 m3 : message, m1 # m2 -> m2 # m3 -> m1 # m3.
Proof.
  intros.  rewrite <- H in H0; auto.
Qed.

(** Equivalence relation [EQb] defined on [Bool] type.  *)

Definition EQb : relation Bool := fun (b1:Bool)  (b2: Bool) =>  [bol (eqb b1 b2)] ~ [ bol TRue].

Infix "##" := EQb (at level 70, right associativity): msg_scope.

Axiom BolEQ: equiv Bool EQb.

Instance Bol_Equ_Equiv : Equivalence  EQb.
Proof.
split;
repeat apply BolEQ.
Qed. 

Theorem EQb_sym: forall b1 b2:Bool, b1 ## b2 -> b2 ## b1.
Proof.
intros.
rewrite H.
reflexivity.
Qed.

Theorem EQb_ref: forall b:Bool, b ## b.
Proof.
intros.
reflexivity.
Qed.

Theorem EQb_trans : forall b1 b2 b3 : Bool, b1 ## b2 -> b2 ## b3 -> b1 ## b3.
Proof.
  intros.  rewrite <- H in H0; auto.
Qed.



(** Equivalence relation [EQos] on [oursum] type. *)

Inductive EQos :  relation oursum := 
|  eqm1: forall (m1 m2: message), m1 # m2 ->  EQos (msg m1) (msg m2)
|  eqb1: forall (b1 b2: Bool), b1 ## b2 ->  EQos (bol b1) (bol b2).

Infix "###" := EQos (at level 0, right associativity):ind_scope.

Instance os_Equ_Equiv : Equivalence  EQos.
Proof. 
split.
unfold Reflexive;
intros;
destruct x;
try apply eqm1; try apply eqb1;
reflexivity.
unfold Symmetric; intros; destruct H;  
    try apply eqm1; try apply eqb1; symmetry; assumption.
unfold Transitive; intros.
  inversion H; subst;
  inversion H0; subst;
  try apply  eqm1; try apply eqb1;   
  rewrite H1;
  apply H3.   

Qed.  
 
Theorem EQos_sym: forall b1 b2: oursum, b1 ### b2 -> b2 ### b1.
Proof.
intros.
rewrite H.
reflexivity.
Qed.

Theorem EQos_ref: forall b:oursum, b ### b.
Proof.
intros.
reflexivity.
Qed.

Theorem EQos_trans : forall b1 b2 b3 : oursum, b1 ### b2 -> b2 ### b3 -> b1 ### b3.
Proof.
  intros.  rewrite <- H in H0; auto.
Qed.
Delimit Scope msg_scope with mor.
(** Equivalence relation [EQosl] is defined on [mylist n] for a natural number [n]. *)

Inductive EQosl: forall {n:nat}, relation (mylist n) :=
| eqnos :  EQosl  (Nil _) (Nil _) 
| eqconos: forall (m:nat)(os1 os2:oursum)(l1 l2: mylist m), os1 ### os2 -> (EQosl  l1  l2) -> EQosl (os1%mor:l1)  (os2%mor:l2).

Infix "####" := EQosl (at level 0, right associativity): ind_scope.

Axiom eqlistos_ind: forall (n:nat) (l1 l2: mylist n), l1 #### l2 ->  l1 ~ l2.

Instance osl_Equ_Equiv : forall {n}, Equivalence  (@EQosl n).
Proof.
split.
  unfold Reflexive. intros.
  induction x.
   apply eqnos.
   apply eqconos. reflexivity.  apply IHx.
 unfold Symmetric.
intros  x y H.
induction H.
apply eqnos.
apply eqconos.
rewrite H. reflexivity. apply IHEQosl.
unfold Transitive.
 intros x y z H1 H2. 
 induction H1. assumption. 
  + dependent destruction z.
     - apply eqconos;    inversion H2; subst. rewrite H. apply H6.
        dependent destruction H2. apply   IHEQosl . assumption.
Qed.


(** Equivalence relation [EQlm] defined on [list message] type. *)

Inductive EQlm:  relation (list message) :=
| eqnm :  EQlm nil nil
| eqconm: forall (m1 m2 : message)(l1 l2: list message),  m1 # m2 -> (EQlm  l1  l2) -> EQlm (cons m1 l1) (cons m2 l2).

Infix "#@" := EQlm (at level 0, right associativity):ind_scope.
                
Axiom eqlistm_ind: forall  (l1 l2:  list message ), l1 #@ l2 ->  (f l1) # (f l2).
Axiom EQlm_Equ_Equiv : Equivalence  (EQlm).
(*Proof.
split.
  unfold Reflexive.
  induction x.
   apply eqnm.
   apply eqconm. reflexivity. apply IHx.
 unfold Symmetric.
intros  x y H.
induction H.
apply eqnm.
apply eqconm.
rewrite H. reflexivity. apply IHEQlm.
unfold Transitive.
 intros x y z H1 H2. 
induction H1; induction H2. apply eqnm. apply eqconm. rewrite H. reflexivity. 
apply IHEQlm.
Admitted.
  *)
Axiom EQlm_equiv:  equiv (list message) (EQlm).

Instance lm_Eqlm_Equiv : Equivalence  (EQlm ).
Proof.
split;
repeat apply EQlm_equiv.
Qed. 

(** * Morhphisms *)

Axiom eq_msg_mylist_cong :  forall  (n n1 :nat) (m1 m2: message) (l1 l2: mylist n), m1 # m2 -> l1 = l2 ->  (submsg_mylist n1 m1 l1) ~ (submsg_mylist n1 m2 l2).

Add Parametric Morphism{n}: (@ submsg_mylist n ) with
  signature eq ==> EQm ==> eq ==> EQI as submsg_mor.
 Proof.   intros. apply eq_msg_mylist_cong;auto. Qed.



(**split.
  unfold Reflexive.
  induction x.
   apply EQNm.

   apply EQCONSm. reflexivity. apply IHx.

 unfold Symmetric.

intros  x y H.

induction H.
apply EQNm.
apply EQCONSm.
rewrite H. reflexivity. apply IHEQlm.

unfold Transitive.
 intros x y z H1 H2. 
 induction H1.
   +  apply H2.
  + dependent destruction z.
     - rewrite <- H2. apply EQCONSm;    inversion H2; subst. rewrite H. apply H6.
        dependent destruction H2. apply   IHEQosl . assumption.
Qed.

Qed.*)


 
(** * [message] *)

 (*
(** [exp_mor] *)
Axiom exp_cong: forall (m1 m2 m3 m1' m2' m3' : message), m1 # m1' -> m2 # m2' -> m3 # m3' -> (exp m1 m2 m3) # (exp m1' m2' m3').
Add Parametric Morphism: (@ exp) with
  signature EQm ==> EQm ==> EQm ==> EQm as exp_mor.
 Proof.   intros. apply exp_cong; assumption. Qed.

  *)
 (** Axioms for Equality *)
Axiom congfm: forall {f} (n n':nat), n = n' -> (f n) # (f n').
Axiom congfb: forall {f} (n n':nat), n = n' -> (f n) ## (f n').
Axiom congf2b: forall {f} (b1 b2 b1' b2':Bool), b1 ## b1' -> b2 ## b2' -> (f b1 b2) ## (f b1' b2').
                                                                         
Axiom congf2mb: forall {f} (m1 m2 m1' m2':message), m1 # m1' -> m2 # m2' -> (f m1 m2) ## (f m1' m2').


Axiom congf3b: forall {f} (b1 b2 b3 b1' b2' b3':Bool), b1 ## b1' -> b2 ## b2' -> b3 ## b3' -> (f b1 b2 b3) ## (f b1' b2' b3').
Axiom congf3mb: forall {f} (m1 m2 m3 m1' m2' m3': message), m1 # m1' -> m2 # m2' -> m3 # m3' -> (f m1 m2 m3) ## (f m1' m2' m3').

Axiom congf4mb: forall {f} (m1 m2 m3 m4 m1' m2' m3' m4': message), m1 # m1' -> m2 # m2' -> m3 # m3' -> m4 # m4' -> (f m1 m2 m3 m4) ## (f m1' m2' m3' m4').

Axiom congf1m: forall {f} (m m':message), m # m' -> (f m) # (f m').
Axiom congf2m: forall {f} (m1 m2 m1' m2':message), m1 # m1' -> m2 # m2' -> (f m1 m2) # (f m1' m2').
Axiom congifm: forall {f} (b1 b1':Bool) (m2 m3 m2' m3':message), b1 ## b1' -> m2 # m2' -> m3 # m3'-> (f b1 m2 m3) # (f b1' m2' m3').

Axiom congf3m: forall {f} (m1 m2 m3 m1' m2' m3':message), m1 # m1' -> m2 # m2' -> m3 # m3'-> (f m1 m2 m3) # (f m1' m2' m3').
Axiom congf4m: forall {f} (m1 m2 m3 m4 m1' m2' m3' m4':message), m1 # m1' -> m2 # m2' -> m3 # m3'-> m4 # m4' -> (f m1 m2 m3 m4) # (f m1' m2' m3' m4').

Axiom congflist: forall (l1 l2:Mlist), l1 = l2 -> (f l1)# (f l2).
 (** [os_cong] *)
 Axiom os_cong: forall (m1 m2: message){n} (l1 l2: mylist n), m1 # m2 -> l1 ~ l2 -> ((msg m1)+++ l1) ~ ((msg m2)+++l2).

Ltac aply_cong := try apply congfm; try apply congfb; try apply congfb; try apply congf2b; try apply congf2mb; try apply congf3b; try apply congf3mb; try apply congf4mb ; try apply congf1m; try apply congf2m; try apply congf3m; try apply congifm; try apply congf4m; try apply congflist; try apply os_cong.
 (** [ifm_mor] *)
 
 
Add Parametric Morphism: (@ifm_then_else_) with
  signature EQb ==> EQm ==> EQm ==> EQm as ifm_then_else_mor.
 Proof.   intros; aply_cong;assumption. Qed.
(** [pair_mor] *)

Add Parametric Morphism: (@ pair) with
  signature EQm ==> EQm ==> EQm as pair_mor.
 Proof.  intros; aply_cong;assumption. Qed.

(** [pi1_mor] *)

Add Parametric Morphism: (@ pi1) with
  signature EQm ==> EQm as pi1_mor.
 Proof.  intros; aply_cong;assumption. Qed.

(** [pi2_mor] *)

Add Parametric Morphism: (@ pi2) with
  signature EQm ==> EQm as pi2_mor.
 Proof.  intros; aply_cong;assumption. Qed.
 
(** [to_mor] *)

Axiom to_cong: forall (m1 m1' : message), m1 # m1' -> (to m1) # (to m1' ).
Add Parametric Morphism: (@ to) with
  signature EQm ==> EQm as to_mor.
Proof.  intros; aply_cong;assumption. Qed.

(** [L_mor] *)

Axiom L_cong: forall (m1  m1'  : message), m1 # m1'  -> (L m1) # (L m1').
Add Parametric Morphism: (@ L) with
  signature EQm ==> EQm as L_mor.
 Proof.  intros; aply_cong;assumption. Qed.
(** [f_m] *)

Axiom f_cong_l : forall (l1 l2: list message) (m1 m2:message), m1 # m2 -> l1 #@ l2   -> (m1 :: l1 ) #@ ( m2:: l2).
Add Parametric Morphism : cons  with
  signature EQm ==> EQlm ==> EQlm as cons_m.
 Proof.    intros. apply f_cong_l. assumption.  assumption. Qed.

Add Parametric Morphism : f  with
  signature EQlm ==> EQm as f_m.
Proof.    intros. apply eqlistm_ind. assumption.   Qed.

(** Vote values *)


Add Parametric Morphism: (@ V0) with
  signature EQm ==> EQm as V0_mor.
Proof.  intros; aply_cong;assumption. Qed.
 

Add Parametric Morphism: (@ V1) with
  signature EQm ==> EQm as V1_mor.
Proof.  intros; aply_cong;assumption. Qed.
(** PubKey *)

Add Parametric Morphism: (@ pubkey) with
  signature EQm ==> EQm as pubkey_mor.
Proof. intros; aply_cong;assumption. Qed.
(** [kc_mor] *)

Add Parametric Morphism: (@ kc) with
  signature EQm ==> EQm as kc_mor.
Proof.  intros; aply_cong;assumption. Qed.


(** foo function symbols *)
(** [comit_mor] *)


Add Parametric Morphism: (@ comm) with
    signature EQm ==> EQm ==> EQm as comit_mor.
Proof.    intros; aply_cong;assumption. Qed.

(** [open_mor] *)


Add Parametric Morphism: (@ open) with
  signature EQm ==> EQm ==> EQm ==> EQm as open_mor.
Proof.  intros; aply_cong;assumption. Qed.


(** [shuf_mor] *)
 
Add Parametric Morphism: (@shufl) with
  signature EQm ==> EQm ==> EQm ==> EQm as shuf_mor.
Proof. intros; aply_cong;assumption. Qed.
 
(** [ke_mor] *)

Add Parametric Morphism: (@ ke) with
  signature EQm ==> EQm as ke_mor.
Proof. intros; aply_cong;assumption. Qed.

(** [re_mor] *)

Add Parametric Morphism: (@ re) with
  signature EQm ==> EQm as re_mor.
Proof. intros; aply_cong;assumption. Qed.

 (** [enc_mor] *)
 
Add Parametric Morphism: (@ enc) with
  signature EQm ==> EQm ==> EQm ==> EQm as enc_mor.
Proof. intros; aply_cong;assumption. Qed.

 (** [dec_mor] *) 
 
Add Parametric Morphism: (@ dec) with
  signature EQm ==> EQm ==> EQm as dec_mor.
Proof. intros; aply_cong;assumption. Qed.
(** Blind Signatures *)
 
(** [kb_mor] *)

Add Parametric Morphism: (@ kb) with
  signature EQm ==> EQm as kb_mor.

  Proof. intros; aply_cong;assumption. Qed.
(** [rb_mor] *)

Add Parametric Morphism: (@ rb) with
      signature EQm ==> EQm as rb_mor.
  Proof. intros; aply_cong;assumption. Qed.
(** [bsign_mor] *)

Add Parametric Morphism: (@bsign) with
  signature EQm ==> EQm ==> EQm ==> EQm as bsign_mor.
Proof. intros; aply_cong;assumption. Qed.
  
(** [bl_mor] *)

Add Parametric Morphism: (@ bl) with
  signature EQm ==> EQm ==> EQm ==> EQm as bl_mor.
Proof. intros; aply_cong;assumption. Qed.
 
(** [ublind_mor] *)

Add Parametric Morphism: (@ ub) with
  signature EQm ==> EQm ==> EQm ==> EQm ==> EQm as ub_mor.
 Proof. intros; aply_cong;assumption. Qed.
(** [acc_mor] *)
(*
Axiom acc_cong: forall (m1 m2 m3 m4  m1' m2' m3' m4' : message), m1 # m1' -> m2 # m2' -> m3 # m3' -> m4 # m4'  -> (acc m1 m2 m3 m4) # (acc m1' m2' m3' m4').
Add Parametric Morphism: (@ acc) with
  signature EQm ==> EQm ==> EQm ==> EQm ==> EQm as acc_mor.
Proof.   intros. apply acc_cong; assumption. Qed.*)
(** [Signatures ] *)
(** [ks_mor] *)
Add Parametric Morphism: (@ ks) with
      signature EQm ==> EQm as ks_mor.
  Proof. intros; aply_cong;assumption. Qed.

(** [rs_mor] *)

Add Parametric Morphism: (@ rs) with
  signature EQm ==> EQm as rs_mor.
Proof. intros; aply_cong;assumption. Qed.

(** [sign_mor] *)

Add Parametric Morphism: (@sign) with
  signature EQm ==> EQm ==> EQm ==> EQm as sign_mor.
Proof. intros; aply_cong;assumption. Qed.



(*
(** [pk_mor] *) 

Axiom pk_cong: forall (n n' : nat), n = n' -> (pk n) # (pk n').
Add Parametric Morphism: (@ pk) with
    signature eq ==> EQm as pk_mor.

Proof. intros; apply pk_cong; reflexivity. Qed.

(** [sk_mor] *)

Axiom sk_cong: forall (n n' : nat), n = n' -> (sk n) # (sk n' ).
Add Parametric Morphism: (@ sk) with
  signature eq ==> EQm as sk_mor.
 Proof.   intros. apply sk_cong. reflexivity. Qed.
*)
 (** [f_mor] *)
 
Axiom f_cong: forall (l1 l1' : list message), ( l1) #@ ( l1') -> (f  l1) # (f  l1' ).
Add Parametric Morphism : ( f ) with
  signature EQlm ==> EQm as f_mor.
Proof.   intros. apply f_cong. auto. Qed.



(** * [Bool] *)

(** [ifb_mor] *)

Add Parametric Morphism: (@ifb_then_else_) with
  signature EQb ==> EQb ==> EQb ==> EQb as ifb_then_else_mor.
 Proof. intros; aply_cong;assumption. Qed.
 


 (** [eqb_mor] *)
 
Add Parametric Morphism: (@eqb) with
signature EQb ==> EQb ==> EQb as eqb_mor.
Proof. intros; aply_cong;assumption. Qed.

(** [eqm_mor] *)


Add Parametric Morphism: (@eqm) with
  signature EQm ==> EQm ==> EQb as eqm_mor.
 Proof. intros; aply_cong;assumption. Qed.

(** [eql_mor] *)

Add Parametric Morphism: (@eql) with
      signature EQm ==> EQm ==> EQb as eql_mor.
Proof. intros; aply_cong;assumption. Qed.

(** [bacc_mor] *)

Add Parametric Morphism: (@acc) with
  signature EQm ==> EQm ==> EQm ==> EQm ==> EQb as acc_mor.
Proof. intros; aply_cong;assumption. Qed.

(** [bver_mor] *)

Add Parametric Morphism: (@bver) with
  signature EQm ==> EQm ==> EQm ==> EQb as bver_mor.
Proof. intros; aply_cong;assumption. Qed.
(** [ver_mor] *)

Add Parametric Morphism: (@ver) with
  signature EQm ==> EQm ==> EQm ==> EQb as ver_mor.
Proof. intros; aply_cong;assumption. Qed.


 Add Parametric Morphism :z  with
  signature EQm ==> EQm as z_mor.
 Proof.  intros; aply_cong;assumption. Qed.


 Axiom cons_cong: forall m1 m2 l1 l2, m1 # m2 -> l1 = l2 -> (cons m1 l1) = (cons m2 l2).
Add Parametric Morphism : cons  with
  signature EQm ==> eq ==> eq as cons_mor.
Proof.   intros. apply cons_cong; auto. Qed.
   Add Parametric Morphism :f  with
  signature eq ==> EQm as f_mor1.
Proof.  intros; aply_cong; try reflexivity. Qed.

(** * Morphisms on substitution functions *)

(** [substbl_bl_mor] *)

Axiom substbl_bl_cong : forall (b1 b2 b1' b2' : Bool) (n: nat), b1 ## b1' -> b2 ## b2' -> (subbol_bol n b1 b2) ## (subbol_bol n b1' b2').

Add Parametric Morphism : (@subbol_bol) with
signature eq ==> EQb ==> EQb ==> EQb as substbl_bl_mor.
Proof. intros; aply_cong;assumption. Qed. 

(** [substbl_msg_mor] *)

Axiom substbl_msg_cong : forall (b1 b1' : Bool)(m2 m2' : message) (n: nat), b1 ## b1' -> m2 # m2' -> (subbol_msg n b1 m2) # (subbol_msg n b1' m2').

Add Parametric Morphism : (@subbol_msg) with
signature eq ==> EQb ==> EQm ==> EQm as substbl_msg_mor.
Proof. intros.  apply substbl_msg_cong. apply H. apply H0.
Qed.

(** [substmsg_Bool_mor] *)

Axiom substmsg_Bool_cong : forall (m1 m1' : message) (b1 b1' : Bool) (n: nat), m1 # m1' -> b1 ## b1' -> (submsg_bol n m1 b1) ## (submsg_bol n m1' b1').

Add Parametric Morphism : (@submsg_bol) with
signature eq ==> EQm ==> EQb ==> EQb as substmsg_Bool_mor.
Proof. intros.  apply substmsg_Bool_cong. apply H. apply H0.
Qed.

(** [substmsg_msg_mor] *)


Add Parametric Morphism : (@submsg_msg) with
signature eq ==> EQm ==> EQm ==> EQm as substmsg_msg_mor.
Proof. intros; aply_cong;assumption. Qed. 

(** [subbol_msg'_mor] *)

Axiom clos_subbol_cong : forall ( b1 b2 b3 b4: Bool) (t1 t2:message), b1 ## b2 -> b3 ## b4 -> t1 # t2 -> (subbol_msg' b1 b3 t1) # (subbol_msg' b2 b4 t2).

Add Parametric Morphism : subbol_msg'  with
  signature EQb ==> EQb ==> EQm ==> EQm as subbol_msg'_mor.
Proof.   intros. apply clos_subbol_cong; try assumption. Qed.




(** * [oursum] *)
(** [msg_mor] *)

Axiom msg_Cong: forall (m1 m1'  : message), m1 # m1'  -> (msg m1 ) ### (msg m1').

Add Parametric Morphism : (@msg ) with
signature EQm ==> EQos as msg_mor.
Proof. intros. apply eqm1. apply H. Qed.

(** [bol_mor] *)

Axiom bol_Cong: forall (b1 b1': Bool), b1 ## b1'  -> (bol b1 ) ### (bol b1').

Add Parametric Morphism : (@bol ) with
signature EQb ==> EQos as bol_mor.
Proof.  intros. apply eqb1. apply H. Qed. 

(** [Cons_mor] *)

Add Parametric Morphism {n}: (Cons oursum n) with
signature EQos ==> EQosl ==> EQosl  as Cons_mor.
Proof. intros. apply eqconos. apply H. apply H0. Qed.

(** [app_EQml_mor] *)

Axiom app_EQml_Cong : forall (n1 n2:nat)(l1 l1'  : mylist n1) (l2 l2': mylist n2), l1 #### l1' -> l2 ####l2' -> (l1 ++ l2) #### (l1' ++ l2').

Add Parametric Morphism {n1} {n2}: (@appMylist n1 n2 ) with
signature  EQosl ==> EQosl ==> EQosl  as app_EQml_mor.
Proof. intros. apply app_EQml_Cong. apply H. apply H0. Qed.

(** [ml_EQI_mor] *)

Axiom ml_EQI_Cong: forall (n : nat) (l1 l2 : mylist n) (os1 os2 : oursum), os1 ### os2 -> l1 ####l2 -> (Cons oursum n os1 l1 ) ~ (Cons  oursum n os2 l2) .

Add Parametric Morphism {n}: (Cons oursum n) with
signature EQos ==> EQosl ==> EQI  as ml_EQI_mor.

Proof. intros. apply ml_EQI_Cong with (os1:=x) (os2:=y) (l1:= x0) (l2:= y0). apply H. apply H0. Qed.

(** [app_EQI_mor] *)

Axiom app_EQI_Cong : forall (n1 n2:nat)(l1 l1'  : mylist n1) (l2 l2': mylist n2), l1 #### l1' -> l2 ####l2' -> (l1 ++ l2) ~ (l1' ++ l2').

Add Parametric Morphism {n1} {n2}: (@appMylist n1 n2 ) with
signature  EQosl ==> EQosl ==> EQI  as app_EQI_mor.
Proof. intros. apply app_EQI_Cong. apply H. apply H0. Qed.




(** Equivalence relation [EQml] on [ilist message n] for given [n]. *)

Definition EQml {n:nat} (l1 l1': ilist message n) :=  (EQosl (conv_mlist_mylist l1) (conv_mlist_mylist l1')).

Infix "==" := EQml (at level 0): ind_scope.

Theorem eqlistm_ind': forall (n:nat) (l1 l2: ilist message n), (l1 == l2) ->  (conv_mlist_mylist l1) ~ (conv_mlist_mylist l2).
Proof. intros. apply eqlistos_ind. apply H. Qed.

Instance ml_Equ_Equiv: forall {n}, Equivalence  (@EQml n).
Proof. 
split.
unfold EQml.
unfold Reflexive. reflexivity.
unfold EQml. unfold Symmetric. intros. rewrite H. reflexivity. 
unfold EQml. unfold Transitive. intros. rewrite H, H0. reflexivity.
Qed.

(** andB_mor *)



Add Parametric Morphism:(@ andB) with 
signature EQb ==> EQb ==> EQb as andB_mor.
Proof. intros; aply_cong;assumption. Qed.

(** notb_mor *) 
 
Add Parametric Morphism: (@ notb) with
signature EQb ==> EQb as notb_mor.
Proof. intros; aply_cong;auto; try reflexivity. Qed.

Print Scope ind_scope.
(*
(** Equality of [Bool] terms using indistinguishability. *)

Definition EQI_bol (b1 b2: Bool) := [ bol (eqb b1 b2)] ~ [bol TRue].

Notation "b1 ## b2" := (EQI_bol b1 b2)(at level 5). 

(** Equality of [message] terms using indistinguishability. *)

Definition EQI_msg (x y : message) :=  [ bol (eqm x y)] ~ [ bol TRue] .

Notation "m1 # m2" := (EQI_msg m1 m2)(at level 5).

(** Attacker starts new session. *)

Definition Att_new_session:= forall x:message,  (eqm (act x) new)  ## TRue .
 *)

