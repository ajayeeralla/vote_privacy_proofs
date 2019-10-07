 
(************************************************************************)
(* Copyright (c) 2017-2018, Ajay Kumar Eeralla <ae266@mail.missouri.edu>*)     
(************************************************************************)
     
Require Export voting_prop.
Require Import Coq.Bool.Bool.
Section lemma14.

  Definition V (b:bool) :=
    match b with
    | false => (V0 (N 0))
    | true => (V1 (N 0))
    end.

  Definition cn (b:bool) :nat :=
    match b with
    | false => 0
    | true => 1
    end.
SearchAbout eqb%bool.
(** abbreviations *)

Definition tau n (m:message) := match n, m with
                                | 1, m => (pi1 m) 
                                | 2, m => (pi1 (pi2 m))
                                | 3, m => (pi2 (pi2 m))
                                | _, _ => O
                                end.

Definition d n x := (dec (tau n x) (ske 2)).
Definition pvchecks x := ((pi2 (d 1 x)) #? TWO) & ((pi2 (d 2 x)) #? TWO) & ((pi2 (d 3 x)) #? TWO).
Definition pochecks x := ((tau 3 (d 1 x)) #? THREE) & ((tau 3 (d 2 x)) #? THREE) & ((tau 3 (d 3 x)) #? THREE).

Definition dist x := !((d 1 x) #? (d 2 x)) & !((d 1 x) #? (d 3 x))& ! ((d 2 x) #? (d 3 x)). 
Definition isin (x y:message):Bool := (x #? (tau 1 y)) or (x #? (tau 2 y)) or (x #? (tau 3 y)).
Definition bcheck (x y:message):Bool := (isin x ((tau 1 (pi2 (tau 1 y))), ((tau 1 (pi2 (tau 2 y))), (tau 1 (pi2 (tau 3 y)))))).
Definition ncheck (x y:message):Bool := (isin x ((tau 3 (pi2 (tau 1 y))), ((tau 3 (pi2 (tau 2 y))), (tau 3 (pi2 (tau 3 y)))))).
 

Definition lbl:= |(N 100)|.
Definition label x y := If (x #? (tau 2 (pi2 (tau 1 y)))) then (pi1 (tau 1 y))
                           else  (If (x#? (tau 2 (pi2 (tau 2 y)))) then (pi1 (tau 2 y))
                                                       else (If (x #? (tau 2 (pi2 (tau 3 y)))) then (pi1 (tau 3 y))
                                                             else O)).

Definition bnlcheck( x y z:message):Bool:= (bcheck x z) & (|(label x z)| #? lbl) & (ncheck y z).

Definition mvchecks x (n n':nat) := (dist (x n n')) & (pvchecks (x n n')).

Definition p n x := ( (tau 1 (d n x)), (tau 2 (d n x))).
 
Definition sotrm x := (shufl (p 1 x) (p 2 x) (p 3 x)).

(** **)

Definition  c j i := (comm (V (xorb j i)) (kc (N ((cn i)+3)))).
Definition pkc := (pke 100).
Definition  b j i := (bl (c j i) pkc (r ((cn i)+1))).
Definition  s j i t0 t1 := ({{ 5 := (b j false) }} ({{ 6:= (b j true) }} (if (eqb i false)%bool then t0 else t1))).
Definition ut j i t0 t1  := (ub (c j i) pkc (r ((cn i)+1)) (s j i t0 t1)).
Definition acct j i t0 t1 := (acc (c j i) pkc (r ((cn i)+1)) (s j i t0 t1)).
Definition e j i  t0 t1 := (enc ((c j i), ((ut j i t0 t1), (N (cn i)))) (pke 11) (er ((cn i)+7))).
Definition e' j i  t0 t1 := (enc ((c j i), ((ut j i t0 t1), (N ((cn i)+100)))) (pke 11) (er ((cn i)+7))).

(** attacker computation *)

Definition phi i := [msg (b i false), msg (b i true)].
Definition phi1 j t0 t1 := (phi j) ++ [msg (e j false t0 t1)].
Definition phi2 j t0 t1 := (phi1 j t0 t1) ++ [msg (e j true t0 t1)].

(** mixer term in the voting phase *)

Definition mvtrm y x :=  If (dist y) & (pvchecks y) then x else |_.

  (** attacker computation *)
  
  Definition phi3 j t0 t1 x := let y:= f (toListm (phi2 j t0 t1)) in
                               (phi2 j t0 t1) ++ [msg (mvtrm y x)].
  (** honest voters' terms of the opening phase *)
 
 Definition l j i t0 t1 x := let f3phi3j:= f (toListm (phi3 j t0 t1 x)) in  If (bnlcheck (c j i) (N (cn i)) f3phi3j) then (enc ((label (c j i) f3phi3j), ((kc (N ((cn i)+3))), THREE))(pke 11) (er ((cn i)+9))) else O.
  Definition phi4 j t0 t1 x := (phi3 j t0 t1 x) ++ [msg (l j false t0 t1 x)].     

  Definition phi5 j t0 t1 x := (phi4 j t0 t1 x) ++ [msg (l j true t0 t1 x)].
                                                                                                                     
  (** mixer term in the opening phase *)

  Definition motrm z  := let Isin i := (isin (k i) ((tau 2 (d 1 z)), ((tau 2 (d 2 z)), (tau 2 (d 3 z))))) in If (dist z) & (pochecks z)& (((Isin 3)&(Isin 4)) or (! ((Isin 3) or (Isin 4)))) then (sotrm z) else O.
  Definition pv j i t0 t1 := ( (c j i), ((ut j i t0 t1), (N (cn i)))).

  (** to apply ENCCCA2 *)

   Definition phi1' j m0 := (phi j) ++ [msg m0] .
   Definition phi2' j t0 t1 m0 := (phi1' j m0) ++ [msg (e j true t0 t1)] .
   Definition phi3' j t0 t1 x m0 := let y:= f (toListm (phi2' j t0 t1 m0)) in
                                 (phi2' j t0 t1 m0) ++ [msg (mvtrm y x)] .
   Definition l' j i t0 t1 x m0 := let f3phi3j:= f (toListm (phi3' j t0 t1 x m0)) in  If (bnlcheck (c j i) (N (cn i)) f3phi3j) then (enc ((label (c j i) f3phi3j), ((kc (N ((cn i)+3))), THREE))(pke 11) (er ((cn i)+9))) else O .
  Definition phi4' j t0 t1 x m0 := (phi3' j t0 t1 x m0) ++ [msg (l' j false t0 t1 x m0)] .
  Definition phi5' j t0 t1 x m0  := (phi4' j t0 t1 x m0) ++ [msg (l' j true t0 t1 x m0)] .
  Definition sj' j t0 t1 m0 := let y:= f (toListm (phi2' j t0 t1 m0)) in (If !(isin (pv j false t0 t1) ((pi1 (d 1 y)), ((pi1 (d 2 y)), (pi1 (d 3 y))))) then (shufl (pi1 (d 1 y)) (pi1 (d 2 y)) (pi1 (d 3 y))) else O)  .
    Definition tl' j t0 t1 m0 := let y:= f (toListm (phi2' j t0 t1 m0)) in
                        let z:= f (toListm (phi5' j t0 t1 (sj' j t0 t1 m0) m0)) in
                        If (acct j false t0 t1) & (acct j true t0 t1) then ( (m0 , ( (e j true t0 t1), (mvtrm y (sj' j t0 t1 m0)))), ((l' j false t0 t1 (sj' j t0 t1 m0) m0), ((l' j true t0 t1 (sj' j t0 t1 m0) m0), (motrm z))))  else O.

  Axiom ENCCCA2' : forall (t0 t1:message) (j:bool),  [msg (b j false), msg (b j true), msg (tl' j t0 t1 (e j false  t0 t1))] ~ [msg (b j false), msg (b j true), msg (tl' j t0 t1 (e' j false  t0 t1))].
                                                                                        
  Lemma replace_first_ballot: 
    forall t0 t1, (Fresh [0; 1; 2; 3; 4] ([msg (pkc), msg (V false), msg (V true), msg t0, msg t1])  = true) ->  closMylist ([msg (pkc)]) = true -> ((length (distMvars [msg t0, msg t1]))=?  2)%nat = true -> bVarMylist [msg t0, msg t1] = nil  ->
    let mvl:= [5; 6] in  (mVarMsg t0) = mvl /\ (mVarMsg t1) = mvl ->
    let sj j t0 t1 := let y:= f (toListm (phi2 j t0 t1)) in (If !(isin (pv j false t0 t1) ((pi1 (d 1 y)), ((pi1 (d 2 y)), (pi1 (d 3 y))))) then (shufl (pi1 (d 1 y)) (pi1 (d 2 y)) (pi1 (d 3 y))) else O)  in
    let tl j t0 t1 := let y:= f (toListm (phi2 j t0 t1)) in
                        let z:= f (toListm (phi5 j t0 t1 (sj j t0 t1))) in
                        If (acct j false t0 t1) & (acct j true t0 t1) then ( ((e j false t0 t1) , ( (e j true t0 t1), (mvtrm y (sj j t0 t1)))), ((l j false t0 t1 (sj j t0 t1)), ((l j true t0 t1 (sj j t0 t1)), (motrm z))))  else O in

let Phi j t0 t1 := [msg (b j false), msg (b j true), msg (tl j t0 t1)] in

   (Phi false t0 t1) ~ (Phi true t0 t1). 
  Proof.                intros. unfold Phi.  unfold tl. simpl. unfold l. unfold sj. simpl.
        
 
                        unfold phi2, sj.
                    
                        pose proof( ENCCCA2' t0 t1 false).
                      
                        assert ( (tl false t0 t1) #  (tl' false t0 t1 (e false false t0 t1))).
                        reflexivity.        rewrite <- H5 in H4; clear H5.
                        pose proof(ENCCCA2' t0 t1 true).
                        assert( (tl' true t0 t1 (e true false t0 t1))# (tl true t0 t1)). reflexivity. rewrite H6 in H5. clear H6.
symmetry in H5.

assert( [msg (b false false), msg (b false true),
       msg (tl' false t0 t1 (e' false false t0 t1))] ~ [msg (b true false), msg (b true true), msg (tl' true t0 t1 (e' true false t0 t1))]).  
unfold tl'. simpl. unfold l'.
unfold bnlcheck.

(** **)

assert ( (ncheck (N (cn false))
                        (f
                           (toListm
                              (phi3' true t0 t1
                                 (sj' true t0 t1 (e' true false t0 t1))
                                 (e' true false t0 t1))))) ## FAlse).


unfold ncheck.  
unfold isin.
assert( (tau 1
      (tau 3 (pi2 (tau 1 (f (toListm (phi3' true t0 t1 (sj' true t0 t1 (e' true false t0 t1)) (e' true false t0 t1)))))),
      (tau 3 (pi2 (tau 2 (f (toListm (phi3' true t0 t1 (sj' true t0 t1 (e' true false t0 t1)) (e' true false t0 t1)))))),
      tau 3 (pi2 (tau 3 (f (toListm (phi3' true t0 t1 (sj' true t0 t1 (e' true false t0 t1)) (e' true false t0 t1))))))))) # (tau 3 (pi2 (tau 1 (f (toListm (phi3' true t0 t1 (sj' true t0 t1 (e' true false t0 t1)) (e' true false t0 t1)))))))).
simpl.
rewrite proj1.
reflexivity.
Axiom eqm_cong: forall m1 m2 m3 m4, m1 # m2 -> m3 # m4 -> (eqm m1 m3) ## (eqm m2 m4).
Set Nested Proofs Allowed.
Add Parametric Morphism: (@ eqm) with
    signature EQm ==> EQm ==> EQb as eqm_mor.
Proof.    intros.  rewrite H, H0. reflexivity.  Qed.
assert(  ((N (cn false)) #?
   (tau 1
      (tau 3 (pi2 (tau 1 (f (toListm (phi3' true t0 t1 (sj' true t0 t1 (e' true false t0 t1)) (e' true false t0 t1)))))),
      (tau 3 (pi2 (tau 2 (f (toListm (phi3' true t0 t1 (sj' true t0 t1 (e' true false t0 t1)) (e' true false t0 t1)))))),
      tau 3 (pi2 (tau 3 (f (toListm (phi3' true t0 t1 (sj' true t0 t1 (e' true false t0 t1)) (e' true false t0 t1)))))))))) ## ((N (cn false)) #? (tau 3 (pi2 (tau 1 (f (toListm (phi3' true t0 t1 (sj' true t0 t1 (e' true false t0 t1)) (e' true false t0 t1))))))))).
rewrite H6.
reflexivity.
Axiom orB_cong: forall b1 b2 b3 b4, b1 ## b2 -> b3 ## b4 -> (IF b1 then TRue else b3) ## (IF b2 then TRue else b4).
Add Parametric Morphism: (@orB) with
      signature EQb ==> EQb ==> EQb as orB_mor.
Proof.  intros. apply orB_cong; auto. Qed.
     rewrite H7. clear H6 H7.
assert( (tau 2
      (tau 3 (pi2 (tau 1 (f (toListm (phi3' true t0 t1 (sj' true t0 t1 (e' true false t0 t1)) (e' true false t0 t1)))))),
      (tau 3 (pi2 (tau 2 (f (toListm (phi3' true t0 t1 (sj' true t0 t1 (e' true false t0 t1)) (e' true false t0 t1)))))),
      tau 3 (pi2 (tau 3 (f (toListm (phi3' true t0 t1 (sj' true t0 t1 (e' true false t0 t1)) (e' true false t0 t1))))))))) # (tau 3 (pi2 (tau 2 (f (toListm (phi3' true t0 t1 (sj' true t0 t1 (e' true false t0 t1)) (e' true false t0 t1)))))))).
simpl.
repeat rewrite proj2.  rewrite proj1. reflexivity.
rewrite H6. clear H6.
assert( (tau 3
      (tau 3 (pi2 (tau 1 (f (toListm (phi3' true t0 t1 (sj' true t0 t1 (e' true false t0 t1)) (e' true false t0 t1)))))),
      (tau 3 (pi2 (tau 2 (f (toListm (phi3' true t0 t1 (sj' true t0 t1 (e' true false t0 t1)) (e' true false t0 t1)))))),
      tau 3 (pi2 (tau 3 (f (toListm (phi3' true t0 t1 (sj' true t0 t1 (e' true false t0 t1)) (e' true false t0 t1))))))))) #  (tau 3 (pi2 (tau 3 (f (toListm (phi3' true t0 t1 (sj' true t0 t1 (e' true false t0 t1)) (e' true false t0 t1)))))))).
simpl.
repeat rewrite proj2. reflexivity.
rewrite H6; clear H6.
pose proof(FRESHNEQ).
Axiom freshneq: forall (n : nat) (m : message),
       ^? (m) = true  ->
       ([bol (N n) #? m]) ~ [bol FAlse].

pose proof(freshneq 0 (tau 3
      (pi2
         (tau 1
            (f
               (toListm
                  (phi3' true t0 t1 (sj' true t0 t1 (e' true false t0 t1)) (e' true false t0 t1)))))))).
simpl in H7.
assert ((^? (s true true t0 t1)) = true).
unfold s.
repeat rewrite clos_sub_vtrm.
reflexivity.
left.
unfold eqb. unfold distMvars.
unfold mVarMylist.
simpl.
inversion H3.
rewrite H9.
reflexivity.
repeat rewrite H8 in H7; clear H8. simpl in H7.
assert( ^? (s true false t0 t1) = true).
unfold s.
repeat rewrite clos_sub_vtrm.
reflexivity.
left.
unfold eqb. unfold distMvars.
unfold mVarMylist.
simpl.
inversion H3.
rewrite H8.
reflexivity.
repeat rewrite H8 in H7; clear H8. simpl in H7.
Axiom consteql: forall x f, const_bol f = true -> [bol x]~[bol f] -> x ## f.
assert( (const_bol FAlse) = true). reflexivity.
apply consteql with (x:= (N 0) #?
           (pi2
              (pi2
                 (pi2
                    (pi1
                       (f
                          [b true false; b true true; e' true false t0 t1; 
                          e true true t0 t1;
                          mvtrm
                            (f [b true false; b true true; e' true false t0 t1; e true true t0 t1])
                            (sj' true t0 t1 (e' true false t0 t1))])))))) in H8.
rewrite H8.
Focus 2.
auto. clear H7 H8.

pose proof( freshneq 0 (tau 3
      (pi2
         (tau 2
            (f
               (toListm
                  (phi3' true t0 t1 (sj' true t0 t1 (e' true false t0 t1)) (e' true false t0 t1)))))))).
simpl in H7.
assert ((^? (s true true t0 t1)) = true).
unfold s.
repeat rewrite clos_sub_vtrm.
reflexivity.
left.
unfold eqb. unfold distMvars.
unfold mVarMylist.
simpl.
inversion H3.
rewrite H9.
reflexivity.
repeat rewrite H8 in H7; clear H8. simpl in H7.
assert( ^? (s true false t0 t1) = true).
unfold s.
repeat rewrite clos_sub_vtrm.
reflexivity.
left.
unfold eqb. unfold distMvars.
unfold mVarMylist.
simpl.
inversion H3.
rewrite H8.
reflexivity.
repeat rewrite H8 in H7; clear H8. simpl in H7.
assert( (const_bol FAlse) = true). reflexivity.
apply consteql with (x:= (N 0) #?
           (pi2
              (pi2
                 (pi2
                    (pi1
                       (pi2
                          (f
                             [b true false; b true true; e' true false t0 t1; 
                             e true true t0 t1;
                             mvtrm
                               (f
                                  [b true false; b true true; e' true false t0 t1;
                                   e true true t0 t1]) (sj' true t0 t1 (e' true false t0 t1))]))))))) in H8.
rewrite H8.
Focus 2.
auto.
clear H7 H8.

pose proof( freshneq 0 (tau 3
     (pi2
        (tau 3
           (f
              (toListm
                 (phi3' true t0 t1 (sj' true t0 t1 (e' true false t0 t1)) (e' true false t0 t1)))))))).
simpl in H7.

assert ((^? (s true true t0 t1)) = true).
unfold s.
repeat rewrite clos_sub_vtrm.
reflexivity.
left.
unfold eqb. unfold distMvars.
unfold mVarMylist.
simpl.
inversion H3.
rewrite H9.
reflexivity.
repeat rewrite H8 in H7; clear H8. simpl in H7.
assert( ^? (s true false t0 t1) = true).
unfold s.
repeat rewrite clos_sub_vtrm.
reflexivity.
left.
unfold eqb. unfold distMvars.
unfold mVarMylist.
simpl.
inversion H3.
rewrite H8.
reflexivity.
repeat rewrite H8 in H7; clear H8. simpl in H7.
assert( (const_bol FAlse) = true). reflexivity.
apply consteql with (x:= (N 0) #?
           (pi2
              (pi2
                 (pi2
                    (pi2
                       (pi2
                          (f
                             [b true false; b true true; e' true false t0 t1; 
                             e true true t0 t1;
                             mvtrm
                               (f
                                  [b true false; b true true; e' true false t0 t1;
                                  e true true t0 t1]) (sj' true t0 t1 (e' true false t0 t1))]))))))) in H8.
Focus 2.
auto.
rewrite H8.
clear H7 H8. unfold orB. repeat rewrite IFFALSE_B.
reflexivity.
rewrite H6.
repeat rewrite andB_FAlse_r.
repeat rewrite IFFALSE_M. 
(** replace *)
assert ( (ncheck (N (cn false))
                     (f
                        (toListm
                           (phi3' false t0 t1 (sj' false t0 t1 (e' false false t0 t1))
                              (e' false false t0 t1))))) ## FAlse).
unfold ncheck.
unfold isin. 
assert( (tau 1
      (tau 3 (pi2 (tau 1 (f (toListm (phi3' false t0 t1 (sj' false t0 t1 (e' false false t0 t1)) (e' false false t0 t1)))))),
      (tau 3 (pi2 (tau 2 (f (toListm (phi3' false t0 t1 (sj' false t0 t1 (e' false false t0 t1)) (e' false false t0 t1)))))),
      tau 3 (pi2 (tau 3 (f (toListm (phi3' false t0 t1 (sj' false t0 t1 (e' false false t0 t1)) (e' false false t0 t1))))))))) # (tau 3 (pi2 (tau 1 (f (toListm (phi3' false t0 t1 (sj' false t0 t1 (e' false false t0 t1)) (e' false false t0 t1)))))))).
unfold tau.
repeat rewrite proj1; try reflexivity.
rewrite H7.
 clear H7.
assert( (tau 2
      (tau 3 (pi2 (tau 1 (f (toListm (phi3' false t0 t1 (sj' false t0 t1 (e' false false t0 t1)) (e' false false t0 t1)))))),
      (tau 3 (pi2 (tau 2 (f (toListm (phi3' false t0 t1 (sj' false t0 t1 (e' false false t0 t1)) (e' false false t0 t1)))))),
      tau 3 (pi2 (tau 3 (f (toListm (phi3' false t0 t1 (sj' false t0 t1 (e' false false t0 t1)) (e' false false t0 t1))))))))) # (tau 3 (pi2 (tau 2 (f (toListm (phi3' false t0 t1 (sj' false t0 t1 (e' false false t0 t1)) (e' false false t0 t1)))))))).
simpl. 
repeat rewrite proj2.  rewrite proj1. reflexivity. 
rewrite H7. clear H7.
assert( (tau 3
      (tau 3 (pi2 (tau 1 (f (toListm (phi3' false t0 t1 (sj' false t0 t1 (e' false false t0 t1)) (e' false false t0 t1)))))),
      (tau 3 (pi2 (tau 2 (f (toListm (phi3' false t0 t1 (sj' false t0 t1 (e' false false t0 t1)) (e' false false t0 t1)))))),
      tau 3 (pi2 (tau 3 (f (toListm (phi3' false t0 t1 (sj' false t0 t1 (e' false false t0 t1)) (e' false false t0 t1))))))))) #  (tau 3 (pi2 (tau 3 (f (toListm (phi3' false t0 t1 (sj' false t0 t1 (e' false false t0 t1)) (e' false false t0 t1)))))))).
simpl.
repeat rewrite proj2. reflexivity.
rewrite H7; clear H7.
 

pose proof(freshneq 0 (tau 3
      (pi2
         (tau 1
            (f
               (toListm
                  (phi3' false t0 t1 (sj' false t0 t1 (e' false false t0 t1))
                     (e' false false t0 t1)))))))).
simpl in H7.

assert ((^? (s false false t0 t1)) = true).
unfold s.
repeat rewrite clos_sub_vtrm.
reflexivity.
left.
unfold eqb. unfold distMvars.
unfold mVarMylist.
simpl.
inversion H3.
rewrite H8.
reflexivity.
repeat rewrite H8 in H7; clear H8. simpl in H7.
assert( ^? (s false true t0 t1) = true).
unfold s.
repeat rewrite clos_sub_vtrm.
reflexivity.
left.
unfold eqb. unfold distMvars.
unfold mVarMylist.
simpl.
inversion H3.
rewrite H9.
reflexivity.
repeat rewrite H8 in H7; clear H8. simpl in H7.



assert( (const_bol FAlse) = true). reflexivity.
apply consteql with (x:= (N 0) #?
           (pi2
              (pi2
                 (pi2
                    (pi1
                       (f
                          [b false false; b false true; e' false false t0 t1; 
                          e false true t0 t1;
                          mvtrm
                            (f
                               [b false false; b false true; e' false false t0 t1;
                               e false true t0 t1]) (sj' false t0 t1 (e' false false t0 t1))])))))) in H8.
Focus 2.
auto.
rewrite H8; clear H7 H8.
pose proof(freshneq 0 (tau 3
      (pi2
         (tau 2
            (f
               (toListm
                  (phi3' false t0 t1 (sj' false t0 t1 (e' false false t0 t1))
                     (e' false false t0 t1)))))))).
simpl in H7.

assert ((^? (s false false t0 t1)) = true).
unfold s.
repeat rewrite clos_sub_vtrm.
reflexivity.
left.
unfold eqb. unfold distMvars.
unfold mVarMylist.
simpl.
inversion H3.
rewrite H8.
reflexivity.
repeat rewrite H8 in H7; clear H8. simpl in H7.
assert( ^? (s false true t0 t1) = true).
unfold s.
repeat rewrite clos_sub_vtrm.
reflexivity.
left.
unfold eqb. unfold distMvars.
unfold mVarMylist.
simpl.
inversion H3.
rewrite H9.
reflexivity.
repeat rewrite H8 in H7; clear H8. simpl in H7.
simpl in H7.


assert( (const_bol FAlse) = true). reflexivity.
apply consteql with (x:= (N 0) #?
           (pi2
              (pi2
                 (pi2
                    (pi1
                       (pi2
                          (f
                             [b false false; b false true; e' false false t0 t1;
                             e false true t0 t1;
                             mvtrm
                               (f
                                  [b false false; b false true; e' false false t0 t1;
                                   e false true t0 t1]) (sj' false t0 t1 (e' false false t0 t1))]))))))) in H8.

Focus 2.
auto.
rewrite H8; clear H7 H8.

pose proof( freshneq 0 (tau 3
     (pi2
        (tau 3
           (f
              (toListm
                 (phi3' false t0 t1 (sj' false t0 t1 (e' false false t0 t1)) (e' false false t0 t1))))))) ).


simpl in H7.


assert ((^? (s false false t0 t1)) = true).
unfold s.
repeat rewrite clos_sub_vtrm.
reflexivity.
left.
unfold eqb. unfold distMvars.
unfold mVarMylist.
simpl.
inversion H3.
rewrite H8.
reflexivity.
repeat rewrite H8 in H7; clear H8. simpl in H7.
assert( ^? (s false true t0 t1) = true).
unfold s.
repeat rewrite clos_sub_vtrm.
reflexivity.
left.
unfold eqb. unfold distMvars.
unfold mVarMylist.
simpl.
inversion H3.
rewrite H9.
reflexivity.
repeat rewrite H8 in H7; clear H8. simpl in H7.



assert( (const_bol FAlse) = true). reflexivity.

apply consteql with (x:= (N 0) #?
           (pi2
              (pi2
                 (pi2
                    (pi2
                       (pi2
                          (f
                             [b false false; b false true; e' false false t0 t1;
                             e false true t0 t1;
                             mvtrm
                               (f
                                  [b false false; b false true; e' false false t0 t1;
                                  e false true t0 t1]) (sj' false t0 t1 (e' false false t0 t1))]))))))) in H8.
Focus 2. auto.

rewrite H8; clear H7 H8.

unfold orB.
repeat rewrite IFFALSE_B.
reflexivity.
unfold phi3'.
simpl. repeat rewrite  H7.
repeat rewrite andB_FAlse_r.

repeat rewrite IFFALSE_M.
unfold motrm.

assert( (isin (k 0)
                     (d 1
                        (f
                           [b false false; b false true; e' false false t0 t1; 
                           e false true t0 t1;
                           mvtrm
                             (f
                                [b false false; b false true; e' false false t0 t1;
                                e false true t0 t1]) (sj' false t0 t1 (e' false false t0 t1)); O;
                           If (bcheck (c false true)
                                 (f
                                    [b false false; b false true; e' false false t0 t1;
                                    e false true t0 t1;
                                    mvtrm
                                      (f
                                         [b false false; b false true; 
                                         e' false false t0 t1; e false true t0 t1])
                                      (sj' false t0 t1 (e' false false t0 t1))])) &
                              ((| label (c false true)
                                    (f
                                       [b false false; b false true; e' false false t0 t1;
                                       e false true t0 t1;
                                       mvtrm
                                         (f
                                            [b false false; b false true; 
                                            e' false false t0 t1; e false true t0 t1])
                                         (sj' false t0 t1 (e' false false t0 t1))]) |) #? lbl) &
                              (ncheck (N 1)
                                 (f
                                    [b false false; b false true; e' false false t0 t1;
                                    e false true t0 t1;
                                    mvtrm
                                      (f
                                         [b false false; b false true; 
                                         e' false false t0 t1; e false true t0 t1])
                                      (sj' false t0 t1 (e' false false t0 t1))]))
                              then (enc (label (c false true)
                                       (f
                                          [b false false; b false true; 
                                          e' false false t0 t1; e false true t0 t1;
                                          mvtrm
                                            (f
                                               [b false false; b false true; 
                                               e' false false t0 t1; e false true t0 t1])
                                            (sj' false t0 t1 (e' false false t0 t1))]),
                                    (kc (N 4), THREE)) (pke 11) (er 10)) 
                              else O]),
                     (d 2
                        (f
                           [b false false; b false true; e' false false t0 t1; 
                           e false true t0 t1;
                           mvtrm
                             (f
                                [b false false; b false true; e' false false t0 t1;
                                e false true t0 t1]) (sj' false t0 t1 (e' false false t0 t1)); O;
                           If (bcheck (c false true)
                                 (f
                                    [b false false; b false true; e' false false t0 t1;
                                    e false true t0 t1;
                                    mvtrm
                                      (f
                                         [b false false; b false true; 
                                         e' false false t0 t1; e false true t0 t1])
                                      (sj' false t0 t1 (e' false false t0 t1))])) &
                              ((| label (c false true)
                                    (f
                                       [b false false; b false true; e' false false t0 t1;
                                       e false true t0 t1;
                                       mvtrm
                                         (f
                                            [b false false; b false true; 
                                            e' false false t0 t1; e false true t0 t1])
                                         (sj' false t0 t1 (e' false false t0 t1))]) |) #? lbl) &
                              (ncheck (N 1)
                                 (f
                                    [b false false; b false true; e' false false t0 t1;
                                    e false true t0 t1;
                                    mvtrm
                                      (f
                                         [b false false; b false true; 
                                         e' false false t0 t1; e false true t0 t1])
                                      (sj' false t0 t1 (e' false false t0 t1))]))
                              then (enc (label (c false true)
                                       (f
                                          [b false false; b false true; 
                                          e' false false t0 t1; e false true t0 t1;
                                          mvtrm
                                            (f
                                               [b false false; b false true; 
                                               e' false false t0 t1; e false true t0 t1])
                                            (sj' false t0 t1 (e' false false t0 t1))]),
                                    (kc (N 4), THREE)) (pke 11) (er 10)) 
                              else O]),
                     d 3
                       (f
                          [b false false; b false true; e' false false t0 t1; 
                          e false true t0 t1;
                          mvtrm
                            (f
                               [b false false; b false true; e' false false t0 t1;
                               e false true t0 t1]) (sj' false t0 t1 (e' false false t0 t1)); O;
                          If (bcheck (c false true)
                                (f
                                   [b false false; b false true; e' false false t0 t1;
                                   e false true t0 t1;
                                   mvtrm
                                     (f
                                        [b false false; b false true; e' false false t0 t1;
                                        e false true t0 t1])
                                     (sj' false t0 t1 (e' false false t0 t1))])) &
                             ((| label (c false true)
                                   (f
                                      [b false false; b false true; e' false false t0 t1;
                                      e false true t0 t1;
                                      mvtrm
                                        (f
                                           [b false false; b false true; 
                                           e' false false t0 t1; e false true t0 t1])
                                        (sj' false t0 t1 (e' false false t0 t1))]) |) #? lbl) &
                             (ncheck (N 1)
                                (f
                                   [b false false; b false true; e' false false t0 t1;
                                   e false true t0 t1;
                                   mvtrm
                                     (f
                                        [b false false; b false true; e' false false t0 t1;
                                        e false true t0 t1])
                                     (sj' false t0 t1 (e' false false t0 t1))]))
                             then (enc (label (c false true)
                                      (f
                                         [b false false; b false true; 
                                         e' false false t0 t1; e false true t0 t1;
                                         mvtrm
                                           (f
                                              [b false false; b false true; 
                                              e' false false t0 t1; e false true t0 t1])
                                           (sj' false t0 t1 (e' false false t0 t1))]),
                                   (kc (N 4), THREE)) (pke 11) (er 10)) 
                             else O])))) ## FAlse).
unfold isin.
unfold d.
unfold tau.
repeat rewrite proj1. repeat rewrite proj2. repeat rewrite proj1.
unfold k.
