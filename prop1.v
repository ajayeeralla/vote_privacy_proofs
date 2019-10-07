 
(************************************************************************)
(* Copyright (c) 2017-2018, Ajay Kumar Eeralla <ae266@mail.missouri.edu>*)     
(************************************************************************)
   
Require Export foo_axioms.
Require Export Coq.Logic.JMeq.
Require Export Coq.Logic.EqdepFacts.
Require Import Omega.
Eval compute in message_beq O O.
Eval compute in message_beq (N 1) (N 2).
(** * Proposition 1 *)
 Section prop. 

   (*Proof. intros. induction t using message_Bool_ind' with (P:=(fun t => exists n, occur_name_msg n t = false)) (P0:=(fun b => exists n, occur_name_bol n b = false)); try exists (n+1); repeat try reflexivity.
        
   Ltac aply_exists := match goal with
                       | [ |- _] =>  exists 3; auto; try reflexivity
                       end.
aply_exists.

Ltac red_occ_n_false:= match goal with
                       | [|- occur_name_msg (?n+1) ?X = false] => induction n; try reflexivity; simpl; auto
                       end.
red_occ_n_false; simpl.  simpl.  simpl in IHt1.
destruct IHt1 as [x]. exists x. rewrite H; clear H.
destruct IHt2 as [x].
intros IHt1.
apply exists in IHt1.
destruct IHt1 as 3.
destruct IHt2 as [3].
destruct IHt3 as [3].
simpl.
exists 3 i IHt1.
 match goal with
    (** Eliminate all existential hypotheses. *)
 | [ H : ex _ |- _ ] => destruct [0  H]
                                        
end.
exists 0.
rewrite IHt1.
Ltac rewriteHyp :=
  match goal with
    | [ H : _ |- _ ] => rewrite H by solve [ auto ]
  end.

rewriteHyp.
rev_hyp.
Ltac aply_Hyp
aply_exists. simpl. induction n. reflexivity. simpl. auto. simpl. rewrite 
   Locate <>.
   SearchAbout beq_nat.
   
   reflexivity.
repeat aply_exists.     *)
             
     (** * Auxiliary Axioms *) 
   Axiom andNotb: forall b1 b2 t0 t1 t2 t3, (If b1&b2 then t0 else (If b1 then t1 else (If b2 then t2 else t3))) # (If b1&b2 then t0 else (If (b1 & ! b2) then t1 else (If (b2& !b1) then t2 else t3))).

   Axiom swapElseBranches: forall b1 b2 t0 t1 t2 t3, (If b1&b2 then t0 else (If b2 then t2 else (If b1 then t1 else t3))) #  (If b1&b2 then t0 else (If b1 then t1 else (If b2 then t2 else t3))).

     Axiom  IFBRANCH_M1': forall {n n1} (ml1 ml2: mylist n) (ml3 ml4: mylist n1) (b b' : Bool)(x x' y y':message), (ml1 ++ ml3 ++ [ bol b , msg x] ) ~  ( ml2 ++ ml4 ++ [ bol b', msg x'])  ->  (ml1 ++ ml3++ [bol b , msg y ] ) ~( ml2 ++ ml4++ [bol b' , msg y']) -> (ml1 ++ ml3++ [msg (If b then x else y)])~ (ml2 ++ ml4++ [msg (If b' then x' else y')]).

   (** * We brought the following changes to the original proposition 

1. We don't emit the commitment key when only one voter moves to the next phase 
2. We also fix the order of emitting the [|_] on the RHS else branches *)

     Axiom DupBoolCond: forall (t1 t2 t3: message) (b:Bool), (If b then t1 else t2) # If b then (If b then t1 else t3) else t2.

  



(** Using [funapptrmhyp] 
Ltac appconst H:=
  funappmconst ok H; funappmconst (V 1) H; funappmconst (V 2) H; funappmconst O H; try reflexivity. *)

(** Axioms *)

 
  Axiom fresh_split : forall (l:Nlist){m n} (z1: mylist m) (z2 : mylist n), Fresh l (z1++z2) = true <-> Fresh l z1 = true /\ Fresh l z2 = true. 
  
   Axiom split_fresh : forall (l1 l2 :Nlist) {n} (z:mylist n), Fresh (l1++l2) z = true -> Fresh l1 z = true /\ Fresh l2 z = true.
   Axiom closMylist_split: forall {m n} (z1 : mylist m) (z2: mylist n), closMylist (z1 ++ z2) = true <-> closMylist z1 = true /\ closMylist z2 = true.

   Axiom gen_ifmf_f1 : forall b t1 t2 {f}, (f (If b then t1 else t2)) # (If b then (f t1) else (f t2)).  
   Axiom gen_ifmf_f2: forall (b:Bool) (t1 t2 t3 : message) {f}, (f (If b then t1 else t2) t3) # If b then (f t1 t3) else (f t2 t3).
   Axiom gen_ifmf_bol_f2: forall (b:Bool) (t1 t2 t3 : message) {f}, (f (If b then t1 else t2) t3) ## IF b then (f t1 t3) else (f t2 t3).
   Axiom gen_ifmf_f2':  forall (b:Bool) (t1 t2 t3 t4: message) {f}, (f (If b then t1 else t2) (If b then t3 else t4)) # (If b then (f t1 t3) else (f t2 t4)).

(** ubNotUndefined_ext is provable from [ubNotUndefined] **)

Axiom ubNotUndefined_ext: forall (t t0 t1 c00 c11 : message) (n1 n2 n5 n6:nat), (Fresh [n1; n2] ([msg t, msg t0, msg t1, msg c00, msg c11])  = true) ->  (closMylist [msg t]) = true -> ((length (distMvars [msg t0, msg t1]))=?  2)%nat = true -> bVarMylist [msg t0, msg t1] = nil  ->
                                                                        let mvl:= [n5; n6] in  (mVarMsg t0) = mvl /\ (mVarMsg t1) = mvl ->
                                                                                              let r0 := (r n1) in
                 let r1 := (r n2) in
                let t2 := ({{ n5 := (bl c00 t r0) }} ({{ n6:=(bl c11 t r1) }} t0)) in
                 let t3 := ({{ n5 := (bl c00 t r0) }} ({{ n6:=(bl c11 t r1) }} t1)) in
                 
(IF (acc c00 t (r n1) t2) & (acc c11 t (r n2) t3)
   then ((ub c00 t (r n1) t2) #? |_) & ((ub c11 t (r n2) t3) #? |_) else TRue) ## notb((acc c00 t (r n1) t2) & (acc c11 t (r n2) t3)).


  Ltac fresh_n n3 n4 H := apply FRESHIND_rs with (n1:= n3) (n2:= n4) in H; try split; try reflexivity.
Ltac funappmconst t H := apply FUNCApp_mconst with (m:= t) in H; simpl in H.
 


Theorem eqmeql: forall (m: message), (m#?m) ## TRue.
Proof. intros.  apply EQmsg; reflexivity. 
Qed.
 


Axiom msg_beq_refl: (forall m, message_beq m m = true).
  

Eval compute in message_beq O O.
Check message_beq.
SearchAbout message_beq.
Print message_beq.
Hint Resolve message_beq.
SearchAbout message.



(*Axiom voteEql : forall x, (|(V0 x)| #? |(V1 x)|) ## TRue. *)

Notation "'[' x '<-' s ']' l" :=  (submsg_mylist x s l).
Axiom extFreshInd: forall {n} n1 n2 n3 (l:mylist n), (Fresh [n1; n2] l) = true -> ((length (distMvars l))<=? 1)%nat = true ->
                                                  (distMvars l) = (cons n3 nil) ->
                                                  ([ n3 <- (N n1)] l) ~ ([n3 <- (N n2)] l).
Fixpoint check_n_occur (n:nat)(nl: Nlist): bool :=
  match nl with
  | [ ] => false
  | h::t => if (beq_nat h n) then true else (check_n_occur n t)
  end.

Axiom n_occ_false: forall n l1 l2, check_n_occur n (l1 ++ l2) = false <-> check_n_occur n l1 = false /\ check_n_occur n l2 = false.

Theorem ifb: forall b:bool, (if b then true else false) = b.
Proof. intros.  destruct b; crush. Qed.
  Theorem sub_ident: forall t n s,  (check_n_occur n (mVarMsg t) = false) -> ({{n:=s}} t) # t.
  Proof. intros.  induction t using message_Bool_ind' with (P:= (fun t =>  (check_n_occur n (mVarMsg t) = false)-> ({{n:=s}} t) # t)) (P0:= (fun b => (check_n_occur n (mVarBol b) = false)-> ([[n:=s]] b)## b)); crush. rewrite PeanoNat.Nat.eqb_sym.
         destruct (n0=?n)%nat. inversion H. reflexivity.
rewrite IHt1, IHt2, IHt3; try apply n_occ_false in H; inversion H; try reflexivity; auto.
apply n_occ_false in H1; inversion H1; auto.
apply n_occ_false in H1; inversion H1; auto.
rewrite IHt1, IHt2; try apply n_occ_false in H; inversion H; try reflexivity; auto.

 simpl.
assert ( check_n_occur n (mapmVarMsg mVarMsg l) = false).
auto.
destruct l; crush. 
Hint Extern 1 (f (match ?LS with nil => _ | cons _ _ => _ end) = _) =>
    destruct LS; crush.
rewrite H2; simpl. simpl.
assert ((map (submsg_msg n s) l) = l).
induction l. reflexivity.
simpl. rewrite IHl. simpl in H3. inversion H3. rewrite H0.  reflexivity.
simpl in H. 
apply n_occ_false with (l1:= mVarMsg m) in H.
inversion H. 
apply n_occ_false in H6. inversion H6 ;auto.
apply n_occ_false. split.
apply n_occ_false in H.  inversion H; auto.

simpl in H. apply n_occ_false in H. inversion H.
apply n_occ_false in H4.
inversion H4. auto.
apply n_occ_false in H.

apply n_occ_false. split. inversion H. auto.
inversion H. simpl in H4.
apply n_occ_false in H4. inversion H4. auto. simpl in H3. apply H3.
rewrite H0.
reflexivity. apply n_occ_false in H; inversion H; auto.

rewrite IHt1, IHt2; try apply n_occ_false in H; inversion H; try reflexivity; auto.

rewrite IHt1, IHt2, IHt3; try apply n_occ_false in H; inversion H; try reflexivity; auto.
apply n_occ_false in H1; inversion H1; auto.
apply n_occ_false in H1; inversion H1; auto.

rewrite IHt1, IHt2, IHt3; try apply n_occ_false in H; inversion H; try reflexivity; auto.
apply n_occ_false in H1; inversion H1; auto.
apply n_occ_false in H1; inversion H1; auto.

rewrite IHt1, IHt2, IHt3; try apply n_occ_false in H; inversion H; try reflexivity; auto.
apply n_occ_false in H1; inversion H1; auto.
apply n_occ_false in H1; inversion H1; auto.


rewrite IHt1, IHt2; try apply n_occ_false in H; inversion H; try reflexivity; auto.

rewrite IHt1, IHt2, IHt3; try apply n_occ_false in H; inversion H; try reflexivity; auto.
apply n_occ_false in H1; inversion H1; auto.
apply n_occ_false in H1; inversion H1; auto.


rewrite IHt1, IHt2, IHt3; try apply n_occ_false in H; inversion H; try reflexivity; auto.
apply n_occ_false in H1; inversion H1; auto.
apply n_occ_false in H1; inversion H1; auto.


rewrite IHt1, IHt2, IHt3, IHt4; try apply n_occ_false in H; inversion H; try reflexivity; auto.
apply n_occ_false in H1; inversion H1; auto.
apply n_occ_false in H3; inversion H3; auto.
apply n_occ_false in H1; inversion H1; auto.
apply n_occ_false in H3; inversion H3; auto.
apply n_occ_false in H1; auto.
inversion H1.
auto.

rewrite IHt1, IHt2, IHt3; try apply n_occ_false in H; inversion H; try reflexivity; auto.
apply n_occ_false in H1; inversion H1; auto.
apply n_occ_false in H1; inversion H1; auto.


Set Nested Proofs Allowed.
Axiom z_cong: forall m1 m2, m1 # m2 -> (z m1) # (z m2).
Add Parametric Morphism: (@z) with
  signature EQm ==> EQm as z_mor.
 Proof.   intros. apply z_cong;auto. Qed.


 rewrite IHt, IHt0; try apply n_occ_false in H; inversion H; try reflexivity; auto.
 rewrite IHt1, IHt2; try apply n_occ_false in H; inversion H; try reflexivity; auto.

rewrite IHt, IHt0, IHt1; try apply n_occ_false in H; inversion H; try reflexivity; auto.
apply n_occ_false in H1; inversion H1; auto.
apply n_occ_false in H1; inversion H1; auto.


rewrite IHt1, IHt2, IHt3, IHt4; try apply n_occ_false in H; inversion H; try reflexivity; auto.
apply n_occ_false in H1; inversion H1; auto.
apply n_occ_false in H3; inversion H3; auto.
apply n_occ_false in H1; inversion H1; auto.
apply n_occ_false in H3; inversion H3; auto.
apply n_occ_false in H1; auto.
inversion H1.
auto.

rewrite IHt1, IHt2, IHt3; try apply n_occ_false in H; inversion H; try reflexivity; auto.
apply n_occ_false in H1; inversion H1; auto.
apply n_occ_false in H1; inversion H1; auto.


rewrite IHt1, IHt2, IHt3; try apply n_occ_false in H; inversion H; try reflexivity; auto.
apply n_occ_false in H1; inversion H1; auto.
apply n_occ_false in H1; inversion H1; auto.
Qed.

 Theorem clos_n_occ_false: forall t n, closMsg t = true ->  check_n_occur n (mVarMsg t) = false.
 Proof.  intros.  induction t using message_Bool_ind' with (P:= (fun t => closMsg t = true ->  check_n_occur n (mVarMsg t) = false)) (P0:= (fun b => closBol b = true -> (check_n_occur n (mVarBol b) = false))); crush.
 apply n_occ_false.
split. apply IHt1. simpl in H.
SearchAbout andb. apply Bool.andb_true_iff in H; inversion H.  apply Bool.andb_true_iff in H0. inversion H0; auto.
apply n_occ_false. split.
rewrite IHt2;try reflexivity.  apply Bool.andb_true_iff in H; inversion H; apply Bool.andb_true_iff in H0; inversion H0; auto.
 apply Bool.andb_true_iff in H; inversion H; apply Bool.andb_true_iff in H0; inversion H0; auto.
 apply n_occ_false; split; apply Bool.andb_true_iff in H; inversion H;auto.
 simpl.
 induction l.
 simpl. reflexivity. simpl.
apply n_occ_false.
split. simpl in H, H0. inversion H0.
apply Bool.andb_true_iff in H. inversion H; apply H1; auto.
apply IHl. simpl in H0.
apply H0. simpl in H. apply Bool.andb_true_iff in H. inversion H; auto.
 apply n_occ_false; split; apply Bool.andb_true_iff in H; inversion H;auto.
 apply n_occ_false; split; try apply IHt1;

 apply Bool.andb_true_iff in H; inversion H; try apply Bool.andb_true_iff in H0; inversion H0; auto.

apply n_occ_false; split; try apply IHt2;

 apply Bool.andb_true_iff in H; inversion H; try apply Bool.andb_true_iff in H0; inversion H0; auto. rewrite H5; auto.

apply n_occ_false; split; try apply IHt1;

 apply Bool.andb_true_iff in H; inversion H; try apply Bool.andb_true_iff in H0; inversion H0; auto.

apply n_occ_false; split; try apply IHt2;

 apply Bool.andb_true_iff in H; inversion H; try apply Bool.andb_true_iff in H0; inversion H0; auto. rewrite H5; auto.

apply n_occ_false; split; try apply IHt1;

 apply Bool.andb_true_iff in H; inversion H; try apply Bool.andb_true_iff in H0; inversion H0; auto.

apply n_occ_false; split; try apply IHt2;

 apply Bool.andb_true_iff in H; inversion H; try apply Bool.andb_true_iff in H0; inversion H0; auto. rewrite H5; auto.
 apply n_occ_false; split; apply Bool.andb_true_iff in H; inversion H;auto.

apply n_occ_false; split; try apply IHt1;

 apply Bool.andb_true_iff in H; inversion H; try apply Bool.andb_true_iff in H0; inversion H0; auto.

apply n_occ_false; split; try apply IHt1;

 apply Bool.andb_true_iff in H; inversion H; try apply Bool.andb_true_iff in H0; inversion H0; auto.


apply n_occ_false; split; apply Bool.andb_true_iff in H; inversion H;auto. simpl. apply IHt1.
apply Bool.andb_true_iff in H0; inversion H0; auto.
apply n_occ_false; split; apply Bool.andb_true_iff in H; inversion H;auto. simpl.
apply IHt2.
apply Bool.andb_true_iff in H0; inversion H0; auto.
repeat (apply n_occ_false; split). 
Ltac rew_hyp:=
repeat match goal with
| [H: context[?n ?X] |- context[?n ?X] ] => rewrite H; try reflexivity
end.
rew_hyp.
 
Ltac rew_andb_t :=
 repeat match goal with
  | [H: context[ (andb ?X ?Y) ] |- _ ] => apply Bool.andb_true_iff in H; inversion H; auto
  end.
rew_andb_t. 
repeat (try rew_hyp; try rew_andb_t).
 (rew_hyp;
rew_andb_t).
rew_hyp. rew_andb_t.
Locate "++".
Ltac rew_n_occ :=
  match goal with
  |[|- context [ app ?X ?Y] ]=> apply n_occ_false; split
  end. 
 rew_n_occ. 
rew_hyp;rew_andb_t.
 rew_n_occ. 
rew_hyp;rew_andb_t.
 
rew_hyp;rew_andb_t. 
 
rew_hyp;rew_andb_t.

 rew_n_occ.
 rew_hyp;rew_andb_t.

 rew_hyp;rew_andb_t.
  rew_n_occ.
rew_hyp;rew_andb_t.

rew_hyp;rew_andb_t.
 rew_n_occ.
rew_hyp;rew_andb_t.

 rew_n_occ.
 rew_hyp;rew_andb_t.
 
rew_hyp;rew_andb_t.

 rew_n_occ.
rew_hyp;rew_andb_t.

 rew_n_occ.
 rew_hyp;rew_andb_t.

  rew_n_occ.
  rew_hyp;rew_andb_t.
  
rew_hyp;rew_andb_t.
 rew_n_occ.
rew_hyp;rew_andb_t.
 rew_n_occ.
rew_hyp;rew_andb_t.

rew_hyp;rew_andb_t.

 rew_n_occ.
rew_hyp;rew_andb_t.

 rew_n_occ.
 rew_hyp;rew_andb_t.
 
rew_hyp;rew_andb_t.
Qed.
Theorem sub_clos: forall n s t, (closMsg t = true) -> ({{ n := s}} t) # t.
Proof. intros. apply clos_n_occ_false with (n:=n) in H. apply sub_ident with (s:=s) in H. auto. Qed.

  Axiom dupBoolSec: forall b1 b2 t1, (IF b1& b2 then t1 else TRue) = (IF b1&b2 then (IF b2 then t1 else FAlse) else TRue).
Axiom dupBoolFirst: forall b1 b2 t1, (IF b1& b2 then t1 else TRue) = (IF b1&b2 then (IF b1 then t1 else FAlse) else TRue).

Axiom aply_f_sub: forall n1 s1 n2 s2 t (f:message-> Nlist), let mvl:= (mVarMsg t) in mvl = [n1; n2] -> (f ({{n1:=s1}} ({{n2:=s2}} t))) = ((f s1) ++ (f s2))%list. 


Axiom sub_in_sub: forall n1 s1  n2 s2 t, {{ n1:= s1}} ({{n2:= s2}} t) # ({{n2:= ({{n1:=s1}} s2)}} ({{n1:=s1}} t)).
Axiom clos_mvars_nil: forall t, (closMsg t = true) -> ((mVarMsg t) = [ ]).
Axiom ext_trans: forall {n} (l1 l2 l3 l4 l5:mylist n), l1 ~l2 /\ l2~ l3 /\ l3~l4 /\ l4~l5 -> l1~l5.
Axiom check_in_sub: forall n s t (f:message->bool), f({{n:=s}} t) = ((f s) && (f t))%bool.
(** nb0:= 1, nb1 = 2, nc0:= 3, nc1:=4 *)

Ltac funappelt n H:= apply FUNCApp_appelt with (p:= n) in H; unfold getelt_at_pos in H; simpl in H.
    
Theorem prop_esorics:  forall (t t0 t1 : message), let v0 := (V0 (N 0)) in
                                                                                                      let v1 := (V1 (N 0)) in
                                                                                                      (|v0|#?|v1|) ## TRue ->  (Fresh [1; 2; 3; 4] ([msg t, msg v0, msg v1, msg t0, msg t1])  = true) ->  closMylist ([msg t]) = true -> ((length (distMvars [msg t0, msg t1]))=?  2)%nat = true -> bVarMylist [msg t0, msg t1] = nil  -> 
    let mvl:= [5; 6] in  (mVarMsg t0) = mvl /\ (mVarMsg t1) = mvl ->
                 let r0 := (r 1) in
                 let r1 := (r 2) in
                 let k0 := (kc (N 3)) in
                 let k1 := (kc (N 4)) in
                 let c00 := (comm v0 k0) in
                 let c01 := (comm v0 k1) in
                 let c10 := (comm v1 k0) in
                 let c11 := (comm v1 k1) in
                 let t2 := ({{ 5 := (bl c00 t r0) }} ({{ 6:=(bl c11 t r1) }} t0)) in
                 let t3 := ({{ 5 := (bl c00 t r0) }} ({{ 6:=(bl c11 t r1) }} t1)) in
                 let t4 := ({{ 5 := (bl c10 t r0) }} ({{ 6:=(bl c01 t r1) }} t0)) in
                 let t5 := ({{ 5 := (bl c10 t r0) }} ({{ 6:=(bl c01 t r1) }} t1)) in
                 let lt1 := (((ub c00 t r0 t2), (c00, k0)), ((ub c11 t r1 t3), (c11, k1)) ) in
                 let lt2 := ((ub c00 t r0 t2), (c00, |_)) in
                 let lt3 := (|_, ((ub c11 t r1 t3), c11)) in
                 let rt1 := (((ub c01 t r1 t5), (c01, k1)), ((ub c10 t r0 t4), (c10, k0))) in
                 let rt2 := (|_, ((ub c01 t r1 t5), c01)) in
                 let rt3 := ((ub c10 t r0 t4), (c10, |_)) in
                 (occur_name_mylist 100 [msg t, msg t0, msg t1] = false) ->
                 ([msg (bl c00 t r0), msg (bl c11 t r1),
                        msg (If (acc c00 t r0 t2)& (acc c11 t r1 t3) then lt1 else (If (acc c00 t r0 t2) then lt2 else (If (acc c11 t r1 t3) then lt3  else (|_, |_))))])
                    ~
                   
                    ([msg (bl c10 t r0), msg (bl c01 t r1),
                           msg (If (acc c10 t r0 t4)& (acc c01 t r1 t5) then rt1 else (If (acc c01 t r1 t5)  then rt2 else (If (acc c10 t r0 t4) then rt3 else (|_, |_))))]). 
Proof. intros  t t0 t1 v0 v1 H H0 H1 H2 H3 mvl H4 r0 r1 k0 k1 c00 c01 c10 c11 t2 t3 t4 t5 lt1 lt2 lt3 rt1 rt2 rt3 nd.
       (** swap inner else branches rt2 and rt3 on the right side *)
       rewrite swapElseBranches with (t1:= rt3). 
       rewrite DupBoolCond with (b:= (acc c00 t r0 t2) & (acc c11 t r1 t3)) (t1:= lt1) (t3:= (|_, (c00, k0), (|_, (c11, k1)))). 
        rewrite DupBoolCond with (b:= (acc c10 t r0 t4) & (acc c01 t r1 t5)) (t1:= rt1) (t3:= (|_, (c01, k1), (|_, (c10, k0)))).
apply IFBRANCH_M1 with (ml1:= [msg (bl c00 t r0), msg (bl c11 t r1)]) (ml2:= [msg (bl c10 t r0), msg (bl c01 t r1)]). simpl.

(** pose proof (blindness). *)
pose proof (blindness 1 2 5 6 c00 c11 t t0 t1 ([ msg c00, msg c11, msg k0, msg k1])). 


assert (BH:   (([msg c00, msg c11, msg k0, msg k1]) ++
        [msg (bl c00 t (r 1)), msg (bl c11 t (r 2)),
        msg
          (If (acc c00 t (r 1)
                 {{5 := bl c00 t (r 1)}} ({{6 := bl c11 t (r 2)}} (t0)))
              &
              (acc c11 t (r 2)
                 {{5 := bl c00 t (r 1)}} ({{6 := bl c11 t (r 2)}} (t1)))
              then (ub c00 t (r 1)
                      {{5
                      := bl c00 t (r 1)}} ({{6 := bl c11 t (r 2)}} (t0)),
                   ub c11 t (r 2)
                     {{5
                     := bl c00 t (r 1)}} ({{6 := bl c11 t (r 2)}} (t1))) 
              else (|_, |_))]) ~
       (([ msg c00, msg c11, msg k0, msg k1]) ++
        [msg (bl c11 t (r 1)), msg (bl c00 t (r 2)),
        msg
          (If (acc c11 t (r 1)
                 {{5 := bl c11 t (r 1)}} ({{6 := bl c00 t (r 2)}} (t0)))
              &
              (acc c00 t (r 2)
                 {{5 := bl c11 t (r 1)}} ({{6 := bl c00 t (r 2)}} (t1)))
              then (ub c00 t (r 2)
                      {{5
                      := bl c11 t (r 1)}} ({{6 := bl c00 t (r 2)}} (t1)),
                   ub c11 t (r 1)
                     {{5
                     := bl c11 t (r 1)}} ({{6 := bl c00 t (r 2)}} (t0))) 
              else (|_, |_))])).
apply H5.     
repeat (apply fresh_split; split). auto.
apply split_fresh with (l1:= [1;2])(l2:=[3;4]) in H0.
inversion H0. 
apply fresh_split with (z1:= [msg t]).
split.

apply fresh_split with (z1:= [msg t]) in H6.
inversion H6. auto.
apply fresh_split with (z1:= [msg c00, msg c11]). split; auto.
apply fresh_split with (z1:= [msg t]) in H6.
inversion H6. auto. simpl. eauto. auto. auto. unfold mvl in H4. auto.
 
 
 clear H5.


(** To construct the acc00 & acc11 term *) 


 simpl in BH.
 
apply FUNCApp_f1 with (f:= pi1) (p:= 7) in BH.
apply FUNCApp_f1 with (f:= pi2) (p:= 8) in BH.

simpl in BH.  


 repeat rewrite gen_ifmf_f1 with (f:= pi1) in BH.
repeat rewrite gen_ifmf_f1 with (f:= pi2) in BH.
repeat rewrite proj1, proj2 in BH. 
funappf2m pair 3 5 BH.
funappf2m pair 3 1 BH.
funappf2m pair 6 8 BH.
funappf2m pair 4 1 BH.
repeat rewrite gen_ifmf_f2 with (f:= pair) in BH. 
funappf2m pair 3 1 BH. 

 rewrite gen_ifmf_f2' with (f:= pair) (t1:= (ub c00 t (r 1) {{5 := bl c00 t (r 1)}} ({{6 := bl c11 t (r 2)}} (t0)), (c00, k0))) in BH.
 rewrite gen_ifmf_f2' with (f:= pair) (t1:= (ub c00 t (r 2) {{5 := bl c11 t (r 1)}} ({{6 := bl c00 t (r 2)}} (t1)), (c00, k0))) in BH.
   
 
 funappmconst |_ BH; auto.
apply FUNCApp_f2b with (f:= eqm) (p1:= 7) (p2:=1) in BH.
simpl in BH.
repeat rewrite gen_ifmf_bol_f2 with (f:= eqm) in BH.


repeat rewrite eqmeql in BH; try auto.



 
rewrite dupBoolSec in BH.
rewrite ubNotUndefined in BH; auto.



rewrite dupBoolFirst with (t1:= (ub c11 t (r 1) {{5 := bl c11 t (r 1)}} ({{6 := bl c00 t (r 2)}} (t0))) #? |_) in BH.
rewrite ubNotUndefined2 in BH; auto. 

Focus 2.
 
apply fresh_split with (z1:= [msg t, msg v0, msg v1, msg t0]) in H0. inversion H0.
apply split_fresh with (l1:= [1;2]) in H5.
inversion H5. simpl.
unfold Fresh in H7.
unfold Fresh.
simpl.
auto.  
Focus 2.
inversion H4. apply H5. 
Focus 2.  unfold Fresh in H0; unfold Fresh. simpl in H0 |- *.
assert(occur_name_msg 1 t = false).
destruct (occur_name_msg 1 t).
inversion H0; auto.
reflexivity. 
assert(occur_name_msg 2 t = false).
destruct (occur_name_msg 2 t). simpl in H0.
SearchAbout orb.
rewrite Bool.orb_true_r in H0. 
inversion H0;  auto. reflexivity.
rewrite H5, H6 in H0 |- *.

assert(occur_name_msg 1 t1 = false).
destruct(occur_name_msg 1 t1).
simpl in H0.
rewrite Bool.orb_true_r in H0. simpl in H0. auto.
reflexivity.
rewrite H7 in H0 |- *. 

assert( occur_name_msg 2 t1 = false).
destruct(occur_name_msg 2 t1).
simpl in H0.
rewrite Bool.orb_true_r in H0.
simpl in H0.
rewrite Bool.orb_true_r in H0.
simpl in H0. inversion H0.
reflexivity.
rewrite H8.
reflexivity.

Focus 2.
inversion H4.
auto.

apply FUNCApp_negpos with (p:= 1) in BH.
simpl in BH. unfold notb in BH.
pose proof(notB_involutive).
unfold notb in H5. unfold notb in BH.
repeat rewrite H5 in BH.
clear H5.


assert(  [msg (bl c00 t (r 1)), msg (bl c11 t (r 2)), bol
           (acc c00 t (r 1) {{5 := bl c00 t (r 1)}} ({{6 := bl c11 t (r 2)}} (t0))) &
           (acc c11 t (r 2) {{5 := bl c00 t (r 1)}} ({{6 := bl c11 t (r 2)}} (t1))),
        msg
          (If (acc c00 t (r 1)
                 {{5 := bl c00 t (r 1)}} ({{6 := bl c11 t (r 2)}} (t0))) &
              (acc c11 t (r 2)
                 {{5 := bl c00 t (r 1)}} ({{6 := bl c11 t (r 2)}} (t1)))
              then (ub c00 t (r 1)
                      {{5 := bl c00 t (r 1)}} ({{6 := bl c11 t (r 2)}} (t0)),
                   (c00, k0),
                   (ub c11 t (r 2)
                      {{5 := bl c00 t (r 1)}} ({{6 := bl c11 t (r 2)}} (t1)),
                   (c11, k1))) 
              else (|_, (c00, k0), (|_, (c11, k1))))] ~ [msg (bl c11 t (r 1)), msg (bl c00 t (r 2)), bol
          (acc c11 t (r 1)
             {{5 := bl c11 t (r 1)}} ({{6 := bl c00 t (r 2)}} (t0))) &
          (acc c00 t (r 2)
             {{5 := bl c11 t (r 1)}} ({{6 := bl c00 t (r 2)}} (t1))),
       msg
         (If (acc c11 t (r 1)
                {{5 := bl c11 t (r 1)}} ({{6 := bl c00 t (r 2)}} (t0))) &
             (acc c00 t (r 2)
                {{5 := bl c11 t (r 1)}} ({{6 := bl c00 t (r 2)}} (t1)))
             then (ub c00 t (r 2)
                     {{5 := bl c11 t (r 1)}} ({{6 := bl c00 t (r 2)}} (t1)),
                  (c00, k0),
                  (ub c11 t (r 1)
                     {{5 := bl c11 t (r 1)}} ({{6 := bl c00 t (r 2)}} (t0)),
                  (c11, k1))) 
             else (|_, (c00, k0), (|_, (c11, k1))))]).
restrsublis BH; simpl; repeat rewrite msg_beq_refl; auto. clear BH.
unfold lt1, rt1.
(** replace c11 --> c10 and c00 --> c01 on the right side of H5 using Fresh indistinguishability*)

(** swap the keys on the right side *)
(** replace N4 with N100 *)
unfold c00, c11, k0, k1 in H5. 
pose proof(extFreshInd 4 100 0 [msg (bl (comm v1 (kc (Mvar 0))) t (r 1)), msg (bl (comm v0 (kc (N 3))) t (r 2)),
       bol
         (acc (comm v1 (kc (Mvar 0))) t (r 1)
            {{5 := bl (comm v1 (kc (Mvar 0))) t (r 1)}} ({{6 := bl (comm v0 (kc (N 3))) t (r 2)}} (t0))) &
         (acc (comm v0 (kc (N 3))) t (r 2)
            {{5 := bl (comm v1 (kc (Mvar 0))) t (r 1)}} ({{6 := bl (comm v0 (kc (N 3))) t (r 2)}} (t1))),
       msg
         (If (acc (comm v1 (kc (Mvar 0))) t (r 1)
                {{5 := bl (comm v1 (kc (Mvar 0))) t (r 1)}} ({{6 := bl (comm v0 (kc (N 3))) t (r 2)}} (t0))) &
             (acc (comm v0 (kc (N 3))) t (r 2)
                {{5 := bl (comm v1 (kc (Mvar 0))) t (r 1)}} ({{6 := bl (comm v0 (kc (N 3))) t (r 2)}} (t1)))
             then (ub (comm v0 (kc (N 3))) t (r 2)
                     {{5 := bl (comm v1 (kc (Mvar 0))) t (r 1)}} ({{6 := bl (comm v0 (kc (N 3))) t (r 2)}} (t1)),
                  (comm v0 (kc (N 3)), kc (N 3)),
                  (ub (comm v1 (kc (Mvar 0))) t (r 1)
                     {{5 := bl (comm v1 (kc (Mvar 0))) t (r 1)}} ({{6 := bl (comm v0 (kc (N 3))) t (r 2)}} (t0)),
                  (comm v1 (kc (Mvar 0)), kc (Mvar 0)))) 
             else (|_, (comm v0 (kc (N 3)), kc (N 3)), (|_, (comm v1 (kc (Mvar 0)), kc (Mvar 0)))))]).
simpl in H6.  
  

repeat  rewrite sub_in_sub with (n1:=0) (t:= ({{6 := bl (comm v0 (kc (N 3))) t (r 2)}} (t1))) in H6.
repeat  rewrite sub_in_sub with (n1:=0) (t:= t1) in H6.
simpl in H6.
do 2 rewrite sub_clos with (n:=0)(t:=t) in H6; simpl in H1; try rewrite Bool.andb_true_r in H1; eauto.
inversion H4.
do 2 rewrite sub_ident with (n:=0) (t:= t1) in H6;  try rewrite H7; try rewrite H8;auto.
                                                                                               
repeat  rewrite sub_in_sub with (n1:=0) (t:= ({{6 := bl (comm v0 (kc (N 3))) t (r 2)}} (t0))) in H6.
repeat  rewrite sub_in_sub with (n1:=0) (t:= t0) in H6.  simpl in H6.
do 2 rewrite sub_ident with (n:=0) (t:= t0) in H6;  try rewrite H7; try rewrite H8;auto.

simpl in H6.
do 2 rewrite sub_clos with (n:=0)(t:=t) in H6; simpl in H1; try rewrite Bool.andb_true_r in H1; eauto.

(** then replace n3 with n4 *)

pose proof (extFreshInd 3 4 0 
[msg (bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))), msg (bl (comm (V0 (N 0)) (kc (Mvar 0))) t (rb (N 2))),
       bol
         (IF acc (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))
               {{5
               := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                    := bl (comm (V0 (N 0)) (kc (Mvar 0))) t (rb (N 2))}} 
                                                                    (t0))
          then acc (comm (V0 (N 0)) (kc (Mvar 0))) t (rb (N 2))
                 {{5
                 := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                      := bl (comm (V0 (N 0)) (kc (Mvar 0))) t (rb (N 2))}} 
                                                                      (t1)) else FAlse),
       msg
         (If IF acc (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))
                  {{5
                  := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                       := bl (comm (V0 (N 0)) (kc (Mvar 0))) t (rb (N 2))}} 
                                                                       (t0))
             then acc (comm (V0 (N 0)) (kc (Mvar 0))) t (rb (N 2))
                    {{5
                    := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                         := bl (comm (V0 (N 0)) (kc (Mvar 0))) t (rb (N 2))}} 
                                                                         (t1)) else FAlse
             then (ub (comm (V0 (N 0)) (kc (Mvar 0))) t (rb (N 2))
                     {{5
                     := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                          := bl (comm (V0 (N 0)) (kc (Mvar 0))) t
                                                                               (rb (N 2))}} 
                                                                          (t1)), (comm (V0 (N 0)) (kc (Mvar 0)), kc (Mvar 0)),
                  (ub (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))
                     {{5
                     := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                          := bl (comm (V0 (N 0)) (kc (Mvar 0))) t
                                                                               (rb (N 2))}} 
                                                                          (t0)),
                  (comm (V1 (N 0)) (kc (N 100)), kc (N 100)))) 
             else (|_, (comm (V0 (N 0)) (kc (Mvar 0)), kc (Mvar 0)), (|_, (comm (V1 (N 0)) (kc (N 100)), kc (N 100)))))]).
simpl in H9.
  

repeat  rewrite sub_in_sub with (n1:=0) (t:= ({{6:= bl (comm (V0 (N 0)) (kc (Mvar 0))) t (rb (N 2))}} t1)) in H9.
repeat  rewrite sub_in_sub with (n1:=0) (t:= t1) in H9.
simpl in H9.
do 2 rewrite sub_clos with (n:=0)(t:=t) in H9; simpl in H1; try rewrite Bool.andb_true_r in H1; eauto.
inversion H4.
do 2 rewrite sub_ident with (n:=0) (t:= t1) in H9;  try rewrite H7; try rewrite H8;auto.
                                                                                                
repeat  rewrite sub_in_sub with (n1:=0) (t:= ({{6 := bl (comm (V0 (N 0)) (kc (Mvar 0))) t (rb (N 2))}} t0))  in H9.
repeat  rewrite sub_in_sub with (n1:=0) (t:= t0) in H9.  simpl in H9.
do 2 rewrite sub_ident with (n:=0) (t:= t0) in H9;  try rewrite H7; try rewrite H8;auto.

simpl in H9.
do 2 rewrite sub_clos with (n:=0)(t:=t) in H9; simpl in H1; try rewrite Bool.andb_true_r in H1; eauto.


(** Finally, replace n100 with n3 *)

pose proof ( extFreshInd 100 3 0 [msg (bl (comm (V1 (N 0)) (kc (Mvar 0))) t (rb (N 1))), msg (bl (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))),
       bol
         (IF acc (comm (V1 (N 0)) (kc (Mvar 0))) t (rb (N 1))
               {{5
               := bl (comm (V1 (N 0)) (kc (Mvar 0))) t (rb (N 1))}} ({{6
                                                                    := bl (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))}} 
                                                                    (t0))
          then acc (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))
                 {{5
                 := bl (comm (V1 (N 0)) (kc (Mvar 0))) t (rb (N 1))}} ({{6
                                                                      := bl (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))}} 
                                                                      (t1)) else FAlse),
       msg
         (If IF acc (comm (V1 (N 0)) (kc (Mvar 0))) t (rb (N 1))
                  {{5
                  := bl (comm (V1 (N 0)) (kc (Mvar 0))) t (rb (N 1))}} ({{6
                                                                       := bl (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))}} 
                                                                       (t0))
             then acc (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))
                    {{5
                    := bl (comm (V1 (N 0)) (kc (Mvar 0))) t (rb (N 1))}} ({{6
                                                                         := bl (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))}} 
                                                                         (t1)) else FAlse
             then (ub (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))
                     {{5
                     := bl (comm (V1 (N 0)) (kc (Mvar 0))) t (rb (N 1))}} ({{6
                                                                          := bl (comm (V0 (N 0)) (kc (N 4))) t
                                                                               (rb (N 2))}} 
                                                                          (t1)), (comm (V0 (N 0)) (kc (N 4)), kc (N 4)),
                  (ub (comm (V1 (N 0)) (kc (Mvar 0))) t (rb (N 1))
                     {{5
                     := bl (comm (V1 (N 0)) (kc (Mvar 0))) t (rb (N 1))}} ({{6
                                                                          := bl (comm (V0 (N 0)) (kc (N 4))) t
                                                                               (rb (N 2))}} 
                                                                          (t0)),
                  (comm (V1 (N 0)) (kc (Mvar 0)), kc (Mvar 0)))) 
             else (|_, (comm (V0 (N 0)) (kc (N 4)), kc (N 4)), (|_, (comm (V1 (N 0)) (kc (Mvar 0)), kc (Mvar 0)))))]).
simpl in H12.


repeat  rewrite sub_in_sub with (n1:=0) (t:= ({{6:= bl (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))}} t1)) in H12.
repeat  rewrite sub_in_sub with (n1:=0) (t:= t1) in H12.
simpl in H12.
do 2 rewrite sub_clos with (n:=0)(t:=t) in H12; simpl in H1; try rewrite Bool.andb_true_r in H1; eauto.

do 2 rewrite sub_ident with (n:=0) (t:= t1) in H12;  try rewrite H7; try rewrite H8;auto.
                                                                                                
repeat  rewrite sub_in_sub with (n1:=0) (t:= ({{6 := bl (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))}} t0))  in H12.
repeat  rewrite sub_in_sub with (n1:=0) (t:= t0) in H12.  simpl in H12.
do 2 rewrite sub_ident with (n:=0) (t:= t0) in H12;  try rewrite H7; try rewrite H8;auto.

simpl in H12.
do 2 rewrite sub_clos with (n:=0)(t:=t) in H12; simpl in H1; try rewrite Bool.andb_true_r in H1; eauto.
fold r0 r1 k0 k1 c00 c11 t2 t3 in H5.
fold k1 in H6.

apply ext_trans with (l2:= [msg (bl c11 t r0), msg (bl c00 t r1),
       bol
         (acc c11 t r0 {{5 := bl c11 t r0}} ({{6 := bl c00 t r1}} (t0))) &
         (acc c00 t r1 {{5 := bl c11 t r0}} ({{6 := bl c00 t r1}} (t1))),
       msg
         (If (acc c11 t r0 {{5 := bl c11 t r0}} ({{6 := bl c00 t r1}} (t0))) &
             (acc c00 t r1 {{5 := bl c11 t r0}} ({{6 := bl c00 t r1}} (t1)))
             then (ub c00 t r1 {{5 := bl c11 t r0}} ({{6 := bl c00 t r1}} (t1)), (c00, k0),
                  (ub c11 t r0 {{5 := bl c11 t r0}} ({{6 := bl c00 t r1}} (t0)), (c11, k1))) 
             else (|_, (c00, k0), (|_, (c11, k1))))]) (l3:= [msg (bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))), msg (bl (comm (V0 (N 0)) (kc (N 3))) t (rb (N 2))),
       bol
         (IF acc (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))
               {{5
               := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                    := bl (comm (V0 (N 0)) (kc (N 3))) t (rb (N 2))}} 
                                                                    (t0))
          then acc (comm (V0 (N 0)) (kc (N 3))) t (rb (N 2))
                 {{5
                 := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                      := bl (comm (V0 (N 0)) (kc (N 3))) t (rb (N 2))}} 
                                                                      (t1)) else FAlse),
       msg
         (If IF acc (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))
                  {{5
                  := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                       := bl (comm (V0 (N 0)) (kc (N 3))) t (rb (N 2))}} 
                                                                       (t0))
             then acc (comm (V0 (N 0)) (kc (N 3))) t (rb (N 2))
                    {{5
                    := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                         := bl (comm (V0 (N 0)) (kc (N 3))) t (rb (N 2))}} 
                                                                         (t1)) else FAlse
             then (ub (comm (V0 (N 0)) (kc (N 3))) t (rb (N 2))
                     {{5
                     := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                          := bl (comm (V0 (N 0)) (kc (N 3))) t
                                                                               (rb (N 2))}} 
                                                                          (t1)), (comm (V0 (N 0)) (kc (N 3)), kc (N 3)),
                  (ub (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))
                     {{5
                     := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                          := bl (comm (V0 (N 0)) (kc (N 3))) t
                                                                               (rb (N 2))}} 
                                                                          (t0)),
                  (comm (V1 (N 0)) (kc (N 100)), kc (N 100)))) 
             else (|_, (comm (V0 (N 0)) (kc (N 3)), kc (N 3)), (|_, (comm (V1 (N 0)) (kc (N 100)), kc (N 100)))))]) (l4:= [msg (bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))), msg (bl (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))),
       bol
         (IF acc (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))
               {{5
               := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                    := bl (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))}} 
                                                                    (t0))
          then acc (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))
                 {{5
                 := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                      := bl (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))}} 
                                                                      (t1)) else FAlse),
       msg
         (If IF acc (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))
                  {{5
                  := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                       := bl (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))}} 
                                                                       (t0))
             then acc (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))
                    {{5
                    := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                         := bl (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))}} 
                                                                         (t1)) else FAlse
             then (ub (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))
                     {{5
                     := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                          := bl (comm (V0 (N 0)) (kc (N 4))) t
                                                                               (rb (N 2))}} 
                                                                          (t1)), (comm (V0 (N 0)) (kc (N 4)), kc (N 4)),
                  (ub (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))
                     {{5
                     := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                          := bl (comm (V0 (N 0)) (kc (N 4))) t
                                                                               (rb (N 2))}} 
                                                                          (t0)),
                  (comm (V1 (N 0)) (kc (N 100)), kc (N 100)))) 
             else (|_, (comm (V0 (N 0)) (kc (N 4)), kc (N 4)), (|_, (comm (V1 (N 0)) (kc (N 100)), kc (N 100)))))]).
repeat split. simpl. unfold lt1. 
apply H5;auto.
apply H6; simpl. unfold Fresh in H0 |- *; auto. simpl.
simpl.

repeat rewrite check_in_sub with (f:= occur_name_msg 100). simpl.
repeat rewrite check_in_sub with (f:= occur_name_msg 4). simpl.

simpl in nd.
assert(occur_name_msg 100 t = false).
destruct (occur_name_msg 100 t). rewrite Bool.orb_true_l in nd. inversion nd. auto. 

repeat rewrite H13.
simpl.
unfold Fresh; simpl in H0.
assert(occur_name_msg 4 t = false).
destruct (occur_name_msg 4 t).
repeat try rewrite Bool.orb_true_l, Bool.orb_true_r in H0.
repeat rewrite Bool.orb_true_r in H0.
inversion H0.
auto.
repeat rewrite H14.
auto.
repeat (try unfold distMvars; try apply clos_mvars_nil in H1; try rewrite aply_f_sub with (f:=mVarMsg); try rewrite H1; simpl; auto).
repeat (try unfold distMvars; try apply clos_mvars_nil in H1; try rewrite aply_f_sub with (f:=mVarMsg); try rewrite H1; simpl; auto).
apply H9.

unfold Fresh;simpl in H0 |- *.
simpl.
repeat rewrite check_in_sub with (f:=occur_name_msg 3).
repeat rewrite check_in_sub with (f:=occur_name_msg 4).
simpl.
unfold Fresh in H0; simpl in H0.
assert(occur_name_msg 3 t = false).
destruct (occur_name_msg 3 t).
simpl.
rewrite Bool.orb_true_l in H0.
repeat rewrite Bool.orb_true_r in H0.
inversion H0. auto.
repeat rewrite H13.
simpl.
assert(occur_name_msg 4 t = false).
destruct (occur_name_msg 4 t).
repeat rewrite Bool.orb_true_l in H0.
repeat rewrite Bool.orb_true_r in H0.
inversion H0. auto.
repeat rewrite H14.
auto.
(** **)
unfold distMvars.
simpl.
repeat rewrite aply_f_sub with (f:=mVarMsg).
simpl.
apply clos_mvars_nil in H1;
try rewrite H1; try auto.
auto.
auto.
(******)
unfold distMvars.
simpl.
repeat rewrite aply_f_sub with (f:=mVarMsg).
simpl.
apply clos_mvars_nil in H1;
try rewrite H1; try auto.
auto.
auto.
apply H12.
(*************************************)
unfold Fresh in H0 |- *; simpl in H0 |- *.
repeat rewrite check_in_sub with (f:=occur_name_msg 3).
repeat rewrite check_in_sub with (f:=occur_name_msg 100).
simpl in nd.
assert(occur_name_msg 100 t = false).
destruct (occur_name_msg 100 t). rewrite Bool.orb_true_l in nd. inversion nd. auto. 

repeat rewrite H13.
simpl.
repeat rewrite H13.
simpl.

unfold Fresh; simpl in H0.
assert(occur_name_msg 3 t = false).
destruct (occur_name_msg 3 t).
repeat try rewrite Bool.orb_true_l, Bool.orb_true_r in H0.
repeat rewrite Bool.orb_true_r in H0.
inversion H0.
auto. 
repeat rewrite H14.
auto.

(************************************)
unfold distMvars.
simpl.
repeat rewrite aply_f_sub with (f:=mVarMsg).
simpl.
apply clos_mvars_nil in H1;
try rewrite H1; try auto.
auto.
auto.

(******)
unfold distMvars.
simpl.
repeat rewrite aply_f_sub with (f:=mVarMsg).
simpl.
apply clos_mvars_nil in H1;
try rewrite H1; try auto.
auto.
auto.



(** 2nd branch *)   
apply IFBRANCH_M1 with (ml1:= [msg (bl c00 t r0), msg (bl c11 t r1), bol (acc c00 t r0 t2) & (acc c11 t r1 t3)]) (ml2:= [msg (bl c10 t r0), msg (bl c01 t r1), bol (acc c10 t r0 t4) & (acc c01 t r1 t5)]).  
unfold lt2, rt3.
unfold t2, t3, t4, t5. 
unfold r0, r1.


pose proof(compHid_ext).
simpl.
pose proof(compHid_ext 3 4 0 1 v0 v1 [] [msg (bl (Mvar 0) t (r 1)), msg (bl (Mvar 1) t (r 2)),
   bol
     (acc (Mvar 0) t (r 1) {{5 := bl (Mvar 0) t (r 1)}} ({{6 := bl (Mvar 1) t (r 2)}} (t0))) &
     (acc (Mvar 1) t (r 2) {{5 := bl (Mvar 0) t (r 1)}} ({{6 := bl (Mvar 1) t (r 2)}} (t1))),
   bol (acc (Mvar 0) t (r 1) {{5 := bl (Mvar 0) t (r 1)}} ({{6 := bl (Mvar 1) t (r 2)}} (t0))),
   msg (ub (Mvar 0) t (r 1) {{5 := bl (Mvar 0) t (r 1)}} ({{6 := bl (Mvar 1) t (r 2)}} (t0)), ((Mvar 0), |_))]).
simpl in H6.  simpl in H1.

SearchAbout andb.
rewrite Bool.andb_true_r in H1.
do 4 rewrite sub_clos with (t:= t) in H6; auto.
simpl in H6. 
  
do 4 rewrite sub_in_sub with (n1:=1)(n2:= 5) in H6.

do 4 rewrite sub_in_sub with (n1:=1)(n2:= 6) in H6.
simpl in H6.

do 2  rewrite sub_clos with (t:= t) in H6; auto.

do 4 rewrite sub_in_sub with (n1:=0)(n2:= 5) in H6.

do 4 rewrite sub_in_sub with (n1:=0)(n2:= 6) in H6.
simpl in H6.

do 2 rewrite sub_clos with (t:= t) in H6; auto.
 



inversion H4.
do 4 rewrite sub_ident with (n:= 1) in H6; try rewrite H7; try rewrite H8; auto.
do 4 rewrite sub_ident with (n:= 0) in H6; try rewrite H7; try rewrite H8; auto. 
simpl in H6.
apply H6.

repeat (try split;auto).
simpl. unfold distMvars. simpl.
simpl. 

repeat rewrite aply_f_sub with (f:= mVarMsg); auto. simpl. 

apply clos_mvars_nil in H1; auto.  
rewrite H1; auto. unfold distMvars. simpl.
repeat rewrite aply_f_sub with (f:=mVarMsg); auto.
apply clos_mvars_nil in H1; simpl;auto. 
rewrite H1; simpl; auto. 
(** 3rd branch *)
simpl.
apply IFBRANCH_M1 with (ml1:= [msg (bl c00 t r0), msg (bl c11 t r1), bol (acc c00 t r0 t2) & (acc c11 t r1 t3), bol (acc c00 t r0 t2)]) (ml2:= [msg (bl c10 t r0), msg (bl c01 t r1), bol (acc c10 t r0 t4) & (acc c01 t r1 t5), bol (acc c10 t r0 t4)]).
simpl.
unfold lt3, rt2.
unfold t2, t3, t4, t5.
pose proof(compHid_ext).
 
pose proof(compHid_ext 3 4 0 1 v0 v1 [] 
[msg (bl (Mvar 0) t r0), msg (bl (Mvar 1) t r1),
   bol
     (acc (Mvar 0) t r0 {{5 := bl (Mvar 0) t r0}} ({{6 := bl (Mvar 1) t r1}} (t0))) &
     (acc (Mvar 1) t r1 {{5 := bl (Mvar 0) t r0}} ({{6 := bl (Mvar 1) t r1}} (t1))),
   bol (acc (Mvar 0) t r0 {{5 := bl (Mvar 0) t r0}} ({{6 := bl (Mvar 1) t r1}} (t0))),
   bol (acc (Mvar 1) t r1 {{5 := bl (Mvar 0) t r0}} ({{6 := bl (Mvar 1) t r1}} (t1))),
   msg (|_, (ub (Mvar 1) t r1 {{5 := bl (Mvar 0) t r0}} ({{6 := bl (Mvar 1) t r1}} (t1)), (Mvar 1)))]).
simpl in H6. simpl in H1.
rewrite Bool.andb_true_r in H1.
do 4 rewrite sub_clos with (t:= t) in H6; auto.
simpl in H6. 
  
do 4 rewrite sub_in_sub with (n1:=1)(n2:= 5) in H6.

do 4 rewrite sub_in_sub with (n1:=1)(n2:= 6) in H6.
simpl in H6.

do 2  rewrite sub_clos with (t:= t) in H6; auto.

do 4 rewrite sub_in_sub with (n1:=0)(n2:= 5) in H6.

do 4 rewrite sub_in_sub with (n1:=0)(n2:= 6) in H6.
simpl in H6.

do 2 rewrite sub_clos with (t:= t) in H6; auto.
inversion H4.
do 4 rewrite sub_ident with (n:= 1) in H6; try rewrite H7; try rewrite H8; auto.
do 4 rewrite sub_ident with (n:= 0) in H6; try rewrite H7; try rewrite H8; auto. 
simpl in H6.
apply H6.

repeat (try split;auto).
simpl. unfold distMvars. simpl.
simpl. 
repeat rewrite aply_f_sub with (f:= mVarMsg); auto. simpl.
apply clos_mvars_nil in H1; auto.  
rewrite H1; auto. unfold distMvars. simpl.
repeat rewrite aply_f_sub with (f:=mVarMsg); auto.
apply clos_mvars_nil in H1; simpl;auto. 
rewrite H1; simpl; auto.
(** final *)
simpl. 
unfold t2, t3, t4, t5.
pose proof(compHid_ext).
pose proof(compHid_ext 3 4 0 1 v0 v1 []
[msg (bl (Mvar 0) t r0), msg (bl (Mvar 1) t r1),
   bol
     (acc (Mvar 0) t r0 {{5 := bl (Mvar 0) t r0}} ({{6 := bl (Mvar 1) t r1}} (t0))) &
     (acc (Mvar 1) t r1 {{5 := bl (Mvar 0) t r0}} ({{6 := bl (Mvar 1) t r1}} (t1))),
   bol (acc (Mvar 0) t r0 {{5 := bl (Mvar 0) t r0}} ({{6 := bl (Mvar 1) t r1}} (t0))),
   bol (acc (Mvar 1) t r1 {{5 := bl (Mvar 0) t r0}} ({{6 := bl (Mvar 1) t r1}} (t1))), msg (|_, |_)]).
simpl in H6. simpl in H1.
rewrite Bool.andb_true_r in H1.
do 4 rewrite sub_clos with (t:= t) in H6; auto.
simpl in H6. 
  
do 4 rewrite sub_in_sub with (n1:=1)(n2:= 5) in H6.

do 4 rewrite sub_in_sub with (n1:=1)(n2:= 6) in H6.
simpl in H6.

do 2  rewrite sub_clos with (t:= t) in H6; auto.

do 4 rewrite sub_in_sub with (n1:=0)(n2:= 5) in H6.

do 4 rewrite sub_in_sub with (n1:=0)(n2:= 6) in H6.
simpl in H6.

do 2 rewrite sub_clos with (t:= t) in H6; auto.
inversion H4.
do 4 rewrite sub_ident with (n:= 1) in H6; try rewrite H7; try rewrite H8; auto.
do 4 rewrite sub_ident with (n:= 0) in H6; try rewrite H7; try rewrite H8; auto. 
simpl in H6.
apply H6.

repeat (try split;auto).
unfold distMvars.
simpl.
repeat rewrite aply_f_sub with (f:= mVarMsg); auto. simpl.
apply clos_mvars_nil in H1; auto.  
rewrite H1; auto. unfold distMvars. simpl.
repeat rewrite aply_f_sub with (f:=mVarMsg); auto.
apply clos_mvars_nil in H1; simpl;auto. 
rewrite H1; simpl; auto.
Qed.

Axiom prop_esorics_gen:  forall {n} (t t0 t1 : message) (z:mylist n), let v0 := (V0 (N 0)) in
                                                                                                      let v1 := (V1 (N 0)) in
                                                                                                      (|v0|#?|v1|) ## TRue ->  (Fresh [1; 2; 3; 4] ([msg t, msg v0, msg v1, msg t0, msg t1])  = true) ->  closMylist ([msg t]) = true -> ((length (distMvars [msg t0, msg t1]))=?  2)%nat = true -> bVarMylist [msg t0, msg t1] = nil  ->
    let mvl:= [5; 6] in  (mVarMsg t0) = mvl /\ (mVarMsg t1) = mvl ->
                 let r0 := (r 1) in
                 let r1 := (r 2) in
                 let k0 := (kc (N 3)) in
                 let k1 := (kc (N 4)) in
                 let c00 := (comm v0 k0) in
                 let c01 := (comm v0 k1) in
                 let c10 := (comm v1 k0) in
                 let c11 := (comm v1 k1) in
                 let t2 := ({{ 5 := (bl c00 t r0) }} ({{ 6:=(bl c11 t r1) }} t0)) in
                 let t3 := ({{ 5 := (bl c00 t r0) }} ({{ 6:=(bl c11 t r1) }} t1)) in
                 let t4 := ({{ 5 := (bl c10 t r0) }} ({{ 6:=(bl c01 t r1) }} t0)) in
                 let t5 := ({{ 5 := (bl c10 t r0) }} ({{ 6:=(bl c01 t r1) }} t1)) in
                 let lt1 := (((ub c00 t r0 t2), (c00, k0)), ((ub c11 t r1 t3), (c11, k1)) ) in
                 let lt2 := ((ub c00 t r0 t2), (c00, |_)) in
                 let lt3 := (|_, ((ub c11 t r1 t3), c11)) in
                 let rt1 := (((ub c01 t r1 t5), (c01, k1)), ((ub c10 t r0 t4), (c10, k0))) in
                 let rt2 := (|_, ((ub c01 t r1 t5), c01)) in
                 let rt3 := ((ub c10 t r0 t4), (c10, |_)) in
                 (occur_name_mylist 100 [msg t, msg t0, msg t1] = false) ->
                 (z++[msg (bl c00 t r0), msg (bl c11 t r1),
                        msg (If (acc c00 t r0 t2)& (acc c11 t r1 t3) then lt1 else (If (acc c00 t r0 t2) then lt2 else (If (acc c11 t r1 t3) then lt3  else (|_, |_))))])
                    ~
                   
                    (z++[msg (bl c10 t r0), msg (bl c01 t r1),
                           msg (If (acc c10 t r0 t4)& (acc c01 t r1 t5) then rt1 else (If (acc c01 t r1 t5)  then rt2 else (If (acc c10 t r0 t4) then rt3 else (|_, |_))))]).
Theorem ext_blind:  forall (t t0 t1 : message), let v0 := (V0 (N 0)) in
                                                                                                      let v1 := (V1 (N 0)) in
                                                                                                      (|v0|#?|v1|) ## TRue ->  (Fresh [1; 2; 3; 4] ([msg t, msg v0, msg v1, msg t0, msg t1])  = true) ->  closMylist ([msg t]) = true -> ((length (distMvars [msg t0, msg t1]))=?  2)%nat = true -> bVarMylist [msg t0, msg t1] = nil  ->
    let mvl:= [5; 6] in  (mVarMsg t0) = mvl /\ (mVarMsg t1) = mvl ->
                 let r0 := (r 1) in
                 let r1 := (r 2) in
                 let k0 := (kc (N 3)) in
                 let k1 := (kc (N 4)) in
                 let c00 := (comm v0 k0) in
                 let c01 := (comm v0 k1) in
                 let c10 := (comm v1 k0) in
                 let c11 := (comm v1 k1) in
                 let t2 := ({{ 5 := (bl c00 t r0) }} ({{ 6:=(bl c11 t r1) }} t0)) in
                 let t3 := ({{ 5 := (bl c00 t r0) }} ({{ 6:=(bl c11 t r1) }} t1)) in
                 let t4 := ({{ 5 := (bl c10 t r0) }} ({{ 6:=(bl c01 t r1) }} t0)) in
                 let t5 := ({{ 5 := (bl c10 t r0) }} ({{ 6:=(bl c01 t r1) }} t1)) in
                 let lt1 := (((ub c00 t r0 t2), (c00, k0)), ((ub c11 t r1 t3), (c11, k1)) ) in
                 let lt2 := ((ub c00 t r0 t2), (c00, |_)) in
                 let lt3 := (|_, ((ub c11 t r1 t3), c11)) in
                 let rt1 := (((ub c01 t r1 t5), (c01, k1)), ((ub c10 t r0 t4), (c10, k0))) in
                 let rt2 := (|_, ((ub c01 t r1 t5), c01)) in
                 let rt3 := ((ub c10 t r0 t4), (c10, |_)) in
                 (occur_name_mylist 100 [msg t, msg t0, msg t1] = false) ->
                 ([msg (bl c00 t r0), msg (bl c11 t r1), bol (acc c00 t r0 t2)& (acc c11 t r1 t3),
                        msg (If (acc c00 t r0 t2)& (acc c11 t r1 t3) then lt1 else (|_, |_))])
                    ~
                   
                    ([msg (bl c10 t r0), msg (bl c01 t r1), bol (acc c10 t r0 t4)& (acc c01 t r1 t5), 
                           msg (If (acc c10 t r0 t4)& (acc c01 t r1 t5) then rt1 else (|_, |_))]).
Proof.   intros  t t0 t1 v0 v1 H H0 H1 H2 H3 mvl H4 r0 r1 k0 k1 c00 c01 c10 c11 t2 t3 t4 t5 lt1 lt2 lt3 rt1 rt2 rt3 nd.
       (** swap inner else branches rt2 and rt3 on the right side *)
       rewrite DupBoolCond with (b:= (acc c00 t r0 t2) & (acc c11 t r1 t3)) (t1:= lt1) (t3:= (|_, (c00, k0), (|_, (c11, k1)))). 
        rewrite DupBoolCond with (b:= (acc c10 t r0 t4) & (acc c01 t r1 t5)) (t1:= rt1) (t3:= (|_, (c01, k1), (|_, (c10, k0)))).
apply IFBRANCH_M1 with (ml1:= [msg (bl c00 t r0), msg (bl c11 t r1), bol (acc c00 t r0 t2) & (acc c11 t r1 t3)]) (ml2:= [msg (bl c10 t r0), msg (bl c01 t r1), bol (acc c10 t r0 t4) & (acc c01 t r1 t5)]). simpl.
unfold lt1, rt1.
(** pose proof (blindness). *)
pose proof (blindness 1 2 5 6 c00 c11 t t0 t1 ([ msg c00, msg c11, msg k0, msg k1])). 


assert (BH:   (([msg c00, msg c11, msg k0, msg k1]) ++
        [msg (bl c00 t (r 1)), msg (bl c11 t (r 2)),
        msg
          (If (acc c00 t (r 1)
                 {{5 := bl c00 t (r 1)}} ({{6 := bl c11 t (r 2)}} (t0)))
              &
              (acc c11 t (r 2)
                 {{5 := bl c00 t (r 1)}} ({{6 := bl c11 t (r 2)}} (t1)))
              then (ub c00 t (r 1)
                      {{5
                      := bl c00 t (r 1)}} ({{6 := bl c11 t (r 2)}} (t0)),
                   ub c11 t (r 2)
                     {{5
                     := bl c00 t (r 1)}} ({{6 := bl c11 t (r 2)}} (t1))) 
              else (|_, |_))]) ~
       (([ msg c00, msg c11, msg k0, msg k1]) ++
        [msg (bl c11 t (r 1)), msg (bl c00 t (r 2)),
        msg
          (If (acc c11 t (r 1)
                 {{5 := bl c11 t (r 1)}} ({{6 := bl c00 t (r 2)}} (t0)))
              &
              (acc c00 t (r 2)
                 {{5 := bl c11 t (r 1)}} ({{6 := bl c00 t (r 2)}} (t1)))
              then (ub c00 t (r 2)
                      {{5
                      := bl c11 t (r 1)}} ({{6 := bl c00 t (r 2)}} (t1)),
                   ub c11 t (r 1)
                     {{5
                     := bl c11 t (r 1)}} ({{6 := bl c00 t (r 2)}} (t0))) 
              else (|_, |_))])).
apply H5.     
repeat (apply fresh_split; split). auto.
apply split_fresh with (l1:= [1;2])(l2:=[3;4]) in H0.
inversion H0. 
apply fresh_split with (z1:= [msg t]).
split.

apply fresh_split with (z1:= [msg t]) in H6.
inversion H6. auto.
apply fresh_split with (z1:= [msg c00, msg c11]). split; auto.
apply fresh_split with (z1:= [msg t]) in H6.
inversion H6. auto. simpl. eauto. auto. auto. unfold mvl in H4. auto.
 
 
 clear H5.


(** To construct the acc00 & acc11 term *) 


 simpl in BH.
 
apply FUNCApp_f1 with (f:= pi1) (p:= 7) in BH.
apply FUNCApp_f1 with (f:= pi2) (p:= 8) in BH.

simpl in BH.  


 repeat rewrite gen_ifmf_f1 with (f:= pi1) in BH.
repeat rewrite gen_ifmf_f1 with (f:= pi2) in BH.
repeat rewrite proj1, proj2 in BH. 
funappf2m pair 3 5 BH.
funappf2m pair 3 1 BH.
funappf2m pair 6 8 BH.
funappf2m pair 4 1 BH.
repeat rewrite gen_ifmf_f2 with (f:= pair) in BH. 
funappf2m pair 3 1 BH. 

 rewrite gen_ifmf_f2' with (f:= pair) (t1:= (ub c00 t (r 1) {{5 := bl c00 t (r 1)}} ({{6 := bl c11 t (r 2)}} (t0)), (c00, k0))) in BH.
 rewrite gen_ifmf_f2' with (f:= pair) (t1:= (ub c00 t (r 2) {{5 := bl c11 t (r 1)}} ({{6 := bl c00 t (r 2)}} (t1)), (c00, k0))) in BH.
   
 
 funappmconst |_ BH; auto.
apply FUNCApp_f2b with (f:= eqm) (p1:= 7) (p2:=1) in BH.
simpl in BH.
repeat rewrite gen_ifmf_bol_f2 with (f:= eqm) in BH.


repeat rewrite eqmeql in BH; try auto.



 
rewrite dupBoolSec in BH.
rewrite ubNotUndefined in BH; auto.



rewrite dupBoolFirst with (t1:= (ub c11 t (r 1) {{5 := bl c11 t (r 1)}} ({{6 := bl c00 t (r 2)}} (t0))) #? |_) in BH.
rewrite ubNotUndefined2 in BH; auto. 

Focus 2.
 
apply fresh_split with (z1:= [msg t, msg v0, msg v1, msg t0]) in H0. inversion H0.
apply split_fresh with (l1:= [1;2]) in H5.
inversion H5. simpl.
unfold Fresh in H7.
unfold Fresh.
simpl.
auto.  
Focus 2.
inversion H4. apply H5. 
Focus 2.  unfold Fresh in H0; unfold Fresh. simpl in H0 |- *.
assert(occur_name_msg 1 t = false).
destruct (occur_name_msg 1 t).
inversion H0; auto.
reflexivity. 
assert(occur_name_msg 2 t = false).
destruct (occur_name_msg 2 t). simpl in H0.
SearchAbout orb.
rewrite Bool.orb_true_r in H0. 
inversion H0;  auto. reflexivity.
rewrite H5, H6 in H0 |- *.

assert(occur_name_msg 1 t1 = false).
destruct(occur_name_msg 1 t1).
simpl in H0.
rewrite Bool.orb_true_r in H0. simpl in H0. auto.
reflexivity.
rewrite H7 in H0 |- *. 

assert( occur_name_msg 2 t1 = false).
destruct(occur_name_msg 2 t1).
simpl in H0.
rewrite Bool.orb_true_r in H0.
simpl in H0.
rewrite Bool.orb_true_r in H0.
simpl in H0. inversion H0.
reflexivity.
rewrite H8.
reflexivity.

Focus 2.
inversion H4.
auto.

apply FUNCApp_negpos with (p:= 1) in BH.
simpl in BH. unfold notb in BH.
pose proof(notB_involutive).
unfold notb in H5. unfold notb in BH.
repeat rewrite H5 in BH.
clear H5.


assert(  [msg (bl c00 t (r 1)), msg (bl c11 t (r 2)), bol
           (acc c00 t (r 1) {{5 := bl c00 t (r 1)}} ({{6 := bl c11 t (r 2)}} (t0))) &
           (acc c11 t (r 2) {{5 := bl c00 t (r 1)}} ({{6 := bl c11 t (r 2)}} (t1))), 
        msg
          (If (acc c00 t (r 1)
                 {{5 := bl c00 t (r 1)}} ({{6 := bl c11 t (r 2)}} (t0))) &
              (acc c11 t (r 2)
                 {{5 := bl c00 t (r 1)}} ({{6 := bl c11 t (r 2)}} (t1)))
              then (ub c00 t (r 1)
                      {{5 := bl c00 t (r 1)}} ({{6 := bl c11 t (r 2)}} (t0)),
                   (c00, k0),
                   (ub c11 t (r 2)
                      {{5 := bl c00 t (r 1)}} ({{6 := bl c11 t (r 2)}} (t1)),
                   (c11, k1))) 
              else (|_, (c00, k0), (|_, (c11, k1))))] ~ [msg (bl c11 t (r 1)), msg (bl c00 t (r 2)), bol
          (acc c11 t (r 1)
             {{5 := bl c11 t (r 1)}} ({{6 := bl c00 t (r 2)}} (t0))) &
          (acc c00 t (r 2)
             {{5 := bl c11 t (r 1)}} ({{6 := bl c00 t (r 2)}} (t1))), 
       msg
         (If (acc c11 t (r 1)
                {{5 := bl c11 t (r 1)}} ({{6 := bl c00 t (r 2)}} (t0))) &
             (acc c00 t (r 2)
                {{5 := bl c11 t (r 1)}} ({{6 := bl c00 t (r 2)}} (t1)))
             then (ub c00 t (r 2)
                     {{5 := bl c11 t (r 1)}} ({{6 := bl c00 t (r 2)}} (t1)),
                  (c00, k0),
                  (ub c11 t (r 1)
                     {{5 := bl c11 t (r 1)}} ({{6 := bl c00 t (r 2)}} (t0)),
                  (c11, k1))) 
             else (|_, (c00, k0), (|_, (c11, k1))))]).
restrsublis BH; simpl; repeat rewrite msg_beq_refl; auto. clear BH.
unfold lt1, rt1.
(** replace c11 --> c10 and c00 --> c01 on the right side of H5 using Fresh indistinguishability*)

(** swap the keys on the right side *)
(** replace N4 with N100 *)
unfold c00, c11, k0, k1 in H5. 
pose proof(extFreshInd 4 100 0 [msg (bl (comm v1 (kc (Mvar 0))) t (r 1)), msg (bl (comm v0 (kc (N 3))) t (r 2)),
       bol
         (acc (comm v1 (kc (Mvar 0))) t (r 1)
            {{5 := bl (comm v1 (kc (Mvar 0))) t (r 1)}} ({{6 := bl (comm v0 (kc (N 3))) t (r 2)}} (t0))) &
         (acc (comm v0 (kc (N 3))) t (r 2)
            {{5 := bl (comm v1 (kc (Mvar 0))) t (r 1)}} ({{6 := bl (comm v0 (kc (N 3))) t (r 2)}} (t1))),
       msg
         (If (acc (comm v1 (kc (Mvar 0))) t (r 1)
                {{5 := bl (comm v1 (kc (Mvar 0))) t (r 1)}} ({{6 := bl (comm v0 (kc (N 3))) t (r 2)}} (t0))) &
             (acc (comm v0 (kc (N 3))) t (r 2)
                {{5 := bl (comm v1 (kc (Mvar 0))) t (r 1)}} ({{6 := bl (comm v0 (kc (N 3))) t (r 2)}} (t1)))
             then (ub (comm v0 (kc (N 3))) t (r 2)
                     {{5 := bl (comm v1 (kc (Mvar 0))) t (r 1)}} ({{6 := bl (comm v0 (kc (N 3))) t (r 2)}} (t1)),
                  (comm v0 (kc (N 3)), kc (N 3)),
                  (ub (comm v1 (kc (Mvar 0))) t (r 1)
                     {{5 := bl (comm v1 (kc (Mvar 0))) t (r 1)}} ({{6 := bl (comm v0 (kc (N 3))) t (r 2)}} (t0)),
                  (comm v1 (kc (Mvar 0)), kc (Mvar 0)))) 
             else (|_, (comm v0 (kc (N 3)), kc (N 3)), (|_, (comm v1 (kc (Mvar 0)), kc (Mvar 0)))))]).
simpl in H6.  
  

repeat  rewrite sub_in_sub with (n1:=0) (t:= ({{6 := bl (comm v0 (kc (N 3))) t (r 2)}} (t1))) in H6.
repeat  rewrite sub_in_sub with (n1:=0) (t:= t1) in H6.
simpl in H6.
do 2 rewrite sub_clos with (n:=0)(t:=t) in H6; simpl in H1; try rewrite Bool.andb_true_r in H1; eauto.
inversion H4.
do 2 rewrite sub_ident with (n:=0) (t:= t1) in H6;  try rewrite H7; try rewrite H8;auto.
                                                                                               
repeat  rewrite sub_in_sub with (n1:=0) (t:= ({{6 := bl (comm v0 (kc (N 3))) t (r 2)}} (t0))) in H6.
repeat  rewrite sub_in_sub with (n1:=0) (t:= t0) in H6.  simpl in H6.
do 2 rewrite sub_ident with (n:=0) (t:= t0) in H6;  try rewrite H7; try rewrite H8;auto.

simpl in H6.
do 2 rewrite sub_clos with (n:=0)(t:=t) in H6; simpl in H1; try rewrite Bool.andb_true_r in H1; eauto.

(** then replace n3 with n4 *)

pose proof (extFreshInd 3 4 0 
[msg (bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))), msg (bl (comm (V0 (N 0)) (kc (Mvar 0))) t (rb (N 2))),
       bol
         (IF acc (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))
               {{5
               := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                    := bl (comm (V0 (N 0)) (kc (Mvar 0))) t (rb (N 2))}} 
                                                                    (t0))
          then acc (comm (V0 (N 0)) (kc (Mvar 0))) t (rb (N 2))
                 {{5
                 := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                      := bl (comm (V0 (N 0)) (kc (Mvar 0))) t (rb (N 2))}} 
                                                                      (t1)) else FAlse),
       msg
         (If IF acc (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))
                  {{5
                  := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                       := bl (comm (V0 (N 0)) (kc (Mvar 0))) t (rb (N 2))}} 
                                                                       (t0))
             then acc (comm (V0 (N 0)) (kc (Mvar 0))) t (rb (N 2))
                    {{5
                    := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                         := bl (comm (V0 (N 0)) (kc (Mvar 0))) t (rb (N 2))}} 
                                                                         (t1)) else FAlse
             then (ub (comm (V0 (N 0)) (kc (Mvar 0))) t (rb (N 2))
                     {{5
                     := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                          := bl (comm (V0 (N 0)) (kc (Mvar 0))) t
                                                                               (rb (N 2))}} 
                                                                          (t1)), (comm (V0 (N 0)) (kc (Mvar 0)), kc (Mvar 0)),
                  (ub (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))
                     {{5
                     := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                          := bl (comm (V0 (N 0)) (kc (Mvar 0))) t
                                                                               (rb (N 2))}} 
                                                                          (t0)),
                  (comm (V1 (N 0)) (kc (N 100)), kc (N 100)))) 
             else (|_, (comm (V0 (N 0)) (kc (Mvar 0)), kc (Mvar 0)), (|_, (comm (V1 (N 0)) (kc (N 100)), kc (N 100)))))]).
simpl in H9.
  

repeat  rewrite sub_in_sub with (n1:=0) (t:= ({{6:= bl (comm (V0 (N 0)) (kc (Mvar 0))) t (rb (N 2))}} t1)) in H9.
repeat  rewrite sub_in_sub with (n1:=0) (t:= t1) in H9.
simpl in H9.
do 2 rewrite sub_clos with (n:=0)(t:=t) in H9; simpl in H1; try rewrite Bool.andb_true_r in H1; eauto.
inversion H4.
do 2 rewrite sub_ident with (n:=0) (t:= t1) in H9;  try rewrite H7; try rewrite H8;auto.
                                                                                                
repeat  rewrite sub_in_sub with (n1:=0) (t:= ({{6 := bl (comm (V0 (N 0)) (kc (Mvar 0))) t (rb (N 2))}} t0))  in H9.
repeat  rewrite sub_in_sub with (n1:=0) (t:= t0) in H9.  simpl in H9.
do 2 rewrite sub_ident with (n:=0) (t:= t0) in H9;  try rewrite H7; try rewrite H8;auto.

simpl in H9.
do 2 rewrite sub_clos with (n:=0)(t:=t) in H9; simpl in H1; try rewrite Bool.andb_true_r in H1; eauto.


(** Finally, replace n100 with n3 *)

pose proof ( extFreshInd 100 3 0 [msg (bl (comm (V1 (N 0)) (kc (Mvar 0))) t (rb (N 1))), msg (bl (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))),
       bol
         (IF acc (comm (V1 (N 0)) (kc (Mvar 0))) t (rb (N 1))
               {{5
               := bl (comm (V1 (N 0)) (kc (Mvar 0))) t (rb (N 1))}} ({{6
                                                                    := bl (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))}} 
                                                                    (t0))
          then acc (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))
                 {{5
                 := bl (comm (V1 (N 0)) (kc (Mvar 0))) t (rb (N 1))}} ({{6
                                                                      := bl (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))}} 
                                                                      (t1)) else FAlse),
       msg
         (If IF acc (comm (V1 (N 0)) (kc (Mvar 0))) t (rb (N 1))
                  {{5
                  := bl (comm (V1 (N 0)) (kc (Mvar 0))) t (rb (N 1))}} ({{6
                                                                       := bl (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))}} 
                                                                       (t0))
             then acc (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))
                    {{5
                    := bl (comm (V1 (N 0)) (kc (Mvar 0))) t (rb (N 1))}} ({{6
                                                                         := bl (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))}} 
                                                                         (t1)) else FAlse
             then (ub (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))
                     {{5
                     := bl (comm (V1 (N 0)) (kc (Mvar 0))) t (rb (N 1))}} ({{6
                                                                          := bl (comm (V0 (N 0)) (kc (N 4))) t
                                                                               (rb (N 2))}} 
                                                                          (t1)), (comm (V0 (N 0)) (kc (N 4)), kc (N 4)),
                  (ub (comm (V1 (N 0)) (kc (Mvar 0))) t (rb (N 1))
                     {{5
                     := bl (comm (V1 (N 0)) (kc (Mvar 0))) t (rb (N 1))}} ({{6
                                                                          := bl (comm (V0 (N 0)) (kc (N 4))) t
                                                                               (rb (N 2))}} 
                                                                          (t0)),
                  (comm (V1 (N 0)) (kc (Mvar 0)), kc (Mvar 0)))) 
             else (|_, (comm (V0 (N 0)) (kc (N 4)), kc (N 4)), (|_, (comm (V1 (N 0)) (kc (Mvar 0)), kc (Mvar 0)))))]).
simpl in H12.


repeat  rewrite sub_in_sub with (n1:=0) (t:= ({{6:= bl (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))}} t1)) in H12.
repeat  rewrite sub_in_sub with (n1:=0) (t:= t1) in H12.
simpl in H12.
do 2 rewrite sub_clos with (n:=0)(t:=t) in H12; simpl in H1; try rewrite Bool.andb_true_r in H1; eauto.

do 2 rewrite sub_ident with (n:=0) (t:= t1) in H12;  try rewrite H7; try rewrite H8;auto.
                                                                                                
repeat  rewrite sub_in_sub with (n1:=0) (t:= ({{6 := bl (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))}} t0))  in H12.
repeat  rewrite sub_in_sub with (n1:=0) (t:= t0) in H12.  simpl in H12.
do 2 rewrite sub_ident with (n:=0) (t:= t0) in H12;  try rewrite H7; try rewrite H8;auto.

simpl in H12.
do 2 rewrite sub_clos with (n:=0)(t:=t) in H12; simpl in H1; try rewrite Bool.andb_true_r in H1; eauto.
fold r0 r1 k0 k1 c00 c11 t2 t3 in H5.
fold k1 in H6.

assert ( [msg (bl c00 t r0), msg (bl c11 t r1), bol (acc c00 t r0 t2) & (acc c11 t r1 t3), 
   msg
     (If (acc c00 t r0 t2) & (acc c11 t r1 t3)
         then (ub c00 t r0 t2, (c00, k0), (ub c11 t r1 t3, (c11, k1))) 
         else (|_, (c00, k0), (|_, (c11, k1))))] ~
  [msg (bl c10 t r0), msg (bl c01 t r1), bol (acc c10 t r0 t4) & (acc c01 t r1 t5), 
  msg
    (If (acc c10 t r0 t4) & (acc c01 t r1 t5)
        then (ub c01 t r1 t5, (c01, k1), (ub c10 t r0 t4, (c10, k0))) 
        else (|_, (c01, k1), (|_, (c10, k0))))]).

apply ext_trans with (l2:= [msg (bl c11 t r0), msg (bl c00 t r1),
       bol
         (acc c11 t r0 {{5 := bl c11 t r0}} ({{6 := bl c00 t r1}} (t0))) &
         (acc c00 t r1 {{5 := bl c11 t r0}} ({{6 := bl c00 t r1}} (t1))),
       msg
         (If (acc c11 t r0 {{5 := bl c11 t r0}} ({{6 := bl c00 t r1}} (t0))) &
             (acc c00 t r1 {{5 := bl c11 t r0}} ({{6 := bl c00 t r1}} (t1)))
             then (ub c00 t r1 {{5 := bl c11 t r0}} ({{6 := bl c00 t r1}} (t1)), (c00, k0),
                  (ub c11 t r0 {{5 := bl c11 t r0}} ({{6 := bl c00 t r1}} (t0)), (c11, k1))) 
             else (|_, (c00, k0), (|_, (c11, k1))))]) (l3:= [msg (bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))), msg (bl (comm (V0 (N 0)) (kc (N 3))) t (rb (N 2))),
       bol
         (IF acc (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))
               {{5
               := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                    := bl (comm (V0 (N 0)) (kc (N 3))) t (rb (N 2))}} 
                                                                    (t0))
          then acc (comm (V0 (N 0)) (kc (N 3))) t (rb (N 2))
                 {{5
                 := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                      := bl (comm (V0 (N 0)) (kc (N 3))) t (rb (N 2))}} 
                                                                      (t1)) else FAlse),
       msg
         (If IF acc (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))
                  {{5
                  := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                       := bl (comm (V0 (N 0)) (kc (N 3))) t (rb (N 2))}} 
                                                                       (t0))
             then acc (comm (V0 (N 0)) (kc (N 3))) t (rb (N 2))
                    {{5
                    := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                         := bl (comm (V0 (N 0)) (kc (N 3))) t (rb (N 2))}} 
                                                                         (t1)) else FAlse
             then (ub (comm (V0 (N 0)) (kc (N 3))) t (rb (N 2))
                     {{5
                     := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                          := bl (comm (V0 (N 0)) (kc (N 3))) t
                                                                               (rb (N 2))}} 
                                                                          (t1)), (comm (V0 (N 0)) (kc (N 3)), kc (N 3)),
                  (ub (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))
                     {{5
                     := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                          := bl (comm (V0 (N 0)) (kc (N 3))) t
                                                                               (rb (N 2))}} 
                                                                          (t0)),
                  (comm (V1 (N 0)) (kc (N 100)), kc (N 100)))) 
             else (|_, (comm (V0 (N 0)) (kc (N 3)), kc (N 3)), (|_, (comm (V1 (N 0)) (kc (N 100)), kc (N 100)))))]) (l4:= [msg (bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))), msg (bl (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))),
       bol
         (IF acc (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))
               {{5
               := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                    := bl (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))}} 
                                                                    (t0))
          then acc (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))
                 {{5
                 := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                      := bl (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))}} 
                                                                      (t1)) else FAlse),
       msg
         (If IF acc (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))
                  {{5
                  := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                       := bl (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))}} 
                                                                       (t0))
             then acc (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))
                    {{5
                    := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                         := bl (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))}} 
                                                                         (t1)) else FAlse
             then (ub (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2))
                     {{5
                     := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                          := bl (comm (V0 (N 0)) (kc (N 4))) t
                                                                               (rb (N 2))}} 
                                                                          (t1)), (comm (V0 (N 0)) (kc (N 4)), kc (N 4)),
                  (ub (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))
                     {{5
                     := bl (comm (V1 (N 0)) (kc (N 100))) t (rb (N 1))}} ({{6
                                                                          := bl (comm (V0 (N 0)) (kc (N 4))) t
                                                                               (rb (N 2))}} 
                                                                          (t0)),
                  (comm (V1 (N 0)) (kc (N 100)), kc (N 100)))) 
             else (|_, (comm (V0 (N 0)) (kc (N 4)), kc (N 4)), (|_, (comm (V1 (N 0)) (kc (N 100)), kc (N 100)))))]).
repeat split. simpl. unfold lt1. 
apply H5;auto.
apply H6; simpl. unfold Fresh in H0 |- *; auto. simpl.
simpl.

repeat rewrite check_in_sub with (f:= occur_name_msg 100). simpl.
repeat rewrite check_in_sub with (f:= occur_name_msg 4). simpl.

simpl in nd.
assert(occur_name_msg 100 t = false).
destruct (occur_name_msg 100 t). rewrite Bool.orb_true_l in nd. inversion nd. auto. 

repeat rewrite H13.
simpl.
unfold Fresh; simpl in H0.
assert(occur_name_msg 4 t = false).
destruct (occur_name_msg 4 t).
repeat try rewrite Bool.orb_true_l, Bool.orb_true_r in H0.
repeat rewrite Bool.orb_true_r in H0.
inversion H0.
auto.
repeat rewrite H14.
auto.
repeat (try unfold distMvars; try apply clos_mvars_nil in H1; try rewrite aply_f_sub with (f:=mVarMsg); try rewrite H1; simpl; auto).
repeat (try unfold distMvars; try apply clos_mvars_nil in H1; try rewrite aply_f_sub with (f:=mVarMsg); try rewrite H1; simpl; auto).
apply H9.

unfold Fresh;simpl in H0 |- *.
simpl.
repeat rewrite check_in_sub with (f:=occur_name_msg 3).
repeat rewrite check_in_sub with (f:=occur_name_msg 4).
simpl.
unfold Fresh in H0; simpl in H0.
assert(occur_name_msg 3 t = false).
destruct (occur_name_msg 3 t).
simpl.
rewrite Bool.orb_true_l in H0.
repeat rewrite Bool.orb_true_r in H0.
inversion H0. auto.
repeat rewrite H13.
simpl.
assert(occur_name_msg 4 t = false).
destruct (occur_name_msg 4 t).
repeat rewrite Bool.orb_true_l in H0.
repeat rewrite Bool.orb_true_r in H0.
inversion H0. auto.
repeat rewrite H14.
auto.
(** **)
unfold distMvars.
simpl.
repeat rewrite aply_f_sub with (f:=mVarMsg).
simpl.
apply clos_mvars_nil in H1;
try rewrite H1; try auto.
auto.
auto.
(******)
unfold distMvars.
simpl.
repeat rewrite aply_f_sub with (f:=mVarMsg).
simpl.
apply clos_mvars_nil in H1;
try rewrite H1; try auto.
auto.
auto.
apply H12.
(*************************************)
unfold Fresh in H0 |- *; simpl in H0 |- *.
repeat rewrite check_in_sub with (f:=occur_name_msg 3).
repeat rewrite check_in_sub with (f:=occur_name_msg 100).
simpl in nd.
assert(occur_name_msg 100 t = false).
destruct (occur_name_msg 100 t). rewrite Bool.orb_true_l in nd. inversion nd. auto. 

repeat rewrite H13.
simpl.
repeat rewrite H13.
simpl.

unfold Fresh; simpl in H0.
assert(occur_name_msg 3 t = false).
destruct (occur_name_msg 3 t).
repeat try rewrite Bool.orb_true_l, Bool.orb_true_r in H0.
repeat rewrite Bool.orb_true_r in H0.
inversion H0.
auto. 
repeat rewrite H14.
auto.

(************************************)
unfold distMvars.
simpl.
repeat rewrite aply_f_sub with (f:=mVarMsg).
simpl.
apply clos_mvars_nil in H1;
try rewrite H1; try auto.
auto.
auto.

(******)
unfold distMvars.
simpl.
repeat rewrite aply_f_sub with (f:=mVarMsg).
simpl.
apply clos_mvars_nil in H1;
try rewrite H1; try auto.
auto.
auto. 

funappelt 3 H13.
restrsublis H13; simpl; repeat rewrite msg_beq_refl; auto.
(** final branch **)
simpl. 
unfold t2, t3, t4, t5.
pose proof(compHid_ext 3 4 0 1 v0 v1 []
[msg (bl (Mvar 0) t r0), msg (bl (Mvar 1) t r1),
   bol
     (acc (Mvar 0) t r0 {{5 := bl (Mvar 0) t r0}} ({{6 := bl (Mvar 1) t r1}} (t0))) &
     (acc (Mvar 1) t r1 {{5 := bl (Mvar 0) t r0}} ({{6 := bl (Mvar 1) t r1}} (t1))), 
   bol (acc (Mvar 0) t r0 {{5 := bl (Mvar 0) t r0}} ({{6 := bl (Mvar 1) t r1}} (t0)))&
    (acc (Mvar 1) t r1 {{5 := bl (Mvar 0) t r0}} ({{6 := bl (Mvar 1) t r1}} (t1))), msg (|_, |_)]).
simpl in H5. simpl in H1.
rewrite Bool.andb_true_r in H1.
do 4 rewrite sub_clos with (t:= t) in H5; auto.
simpl in H5. 
  
do 4 rewrite sub_in_sub with (n1:=1)(n2:= 5) in H5.

do 4 rewrite sub_in_sub with (n1:=1)(n2:= 6) in H5.
simpl in H5.

do 2  rewrite sub_clos with (t:= t) in H5; auto.

do 4 rewrite sub_in_sub with (n1:=0)(n2:= 5) in H5.

do 4 rewrite sub_in_sub with (n1:=0)(n2:= 6) in H5.
simpl in H5.

do 2 rewrite sub_clos with (t:= t) in H5; auto.
inversion H4. 
do 4 rewrite sub_ident with (n:= 1) in H5; try rewrite H6; try rewrite H7; auto.
do 4 rewrite sub_ident with (n:= 0) in H5; try rewrite H6; try rewrite H7; auto. 
 simpl in H5. simpl in H5. simpl. unfold r0, r1. 
apply H5.

repeat (try split;auto).
unfold distMvars.
simpl.
repeat rewrite aply_f_sub with (f:= mVarMsg); auto. simpl.
apply clos_mvars_nil in H1; auto.  
rewrite H1; auto. unfold distMvars. simpl.
repeat rewrite aply_f_sub with (f:=mVarMsg); auto.
apply clos_mvars_nil in H1; simpl;auto. 
rewrite H1; simpl; auto.
Qed.

Axiom ext_blind_gen:  forall {n} (t t0 t1 : message) (z:mylist n), let v0 := (V0 (N 0)) in
                                                                                                      let v1 := (V1 (N 0)) in
                                                                                                      (|v0|#?|v1|) ## TRue ->  (Fresh [1; 2; 3; 4] ([msg t, msg v0, msg v1, msg t0, msg t1])  = true) ->  closMylist ([msg t]) = true -> ((length (distMvars [msg t0, msg t1]))=?  2)%nat = true -> bVarMylist [msg t0, msg t1] = nil  ->
    let mvl:= [5; 6] in  (mVarMsg t0) = mvl /\ (mVarMsg t1) = mvl ->
                 let r0 := (r 1) in
                 let r1 := (r 2) in
                 let k0 := (kc (N 3)) in
                 let k1 := (kc (N 4)) in
                 let c00 := (comm v0 k0) in
                 let c01 := (comm v0 k1) in
                 let c10 := (comm v1 k0) in
                 let c11 := (comm v1 k1) in
                 let t2 := ({{ 5 := (bl c00 t r0) }} ({{ 6:=(bl c11 t r1) }} t0)) in
                 let t3 := ({{ 5 := (bl c00 t r0) }} ({{ 6:=(bl c11 t r1) }} t1)) in
                 let t4 := ({{ 5 := (bl c10 t r0) }} ({{ 6:=(bl c01 t r1) }} t0)) in
                 let t5 := ({{ 5 := (bl c10 t r0) }} ({{ 6:=(bl c01 t r1) }} t1)) in
                 let lt1 := (((ub c00 t r0 t2), (c00, k0)), ((ub c11 t r1 t3), (c11, k1)) ) in
                 let lt2 := ((ub c00 t r0 t2), (c00, |_)) in
                 let lt3 := (|_, ((ub c11 t r1 t3), c11)) in
                 let rt1 := (((ub c01 t r1 t5), (c01, k1)), ((ub c10 t r0 t4), (c10, k0))) in
                 let rt2 := (|_, ((ub c01 t r1 t5), c01)) in
                 let rt3 := ((ub c10 t r0 t4), (c10, |_)) in
                 (occur_name_mylist 100 [msg t, msg t0, msg t1] = false) ->
                 (z++[msg (bl c00 t r0), msg (bl c11 t r1), bol (acc c00 t r0 t2)& (acc c11 t r1 t3),
                        msg (If (acc c00 t r0 t2)& (acc c11 t r1 t3) then lt1 else (|_, |_))])
                    ~
                   
                    (z++[msg (bl c10 t r0), msg (bl c01 t r1), bol (acc c10 t r0 t4)& (acc c01 t r1 t5), 
                           msg (If (acc c10 t r0 t4)& (acc c01 t r1 t5) then rt1 else (|_, |_))]).
End prop.