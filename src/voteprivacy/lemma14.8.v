 
(************************************************************************)
(* Copyright (c) 2017-2018, Ajay Kumar Eeralla <ae266@mail.missouri.edu>*)     
(************************************************************************)
     
Require Export extfuncapp.
Require Import Coq.Bool.Bool.
Set Nested Proofs Allowed.
Section lemma148.

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

Definition isink (x y:message):Bool := (x #? (tau 2 (d 1 y))) or (x #? (tau 2 (d 2 y))) or (x #? (tau 2 (d 3 y))).
(** **)
Axiom funcapp_f1m': forall {n n'} f p1 (z z':mylist n) (z1 z1':mylist n'), (z ++ z1) ~ (z' ++ z1') -> ((z ++ z1) ++ [msg (f (ostomsg (getelt_at_pos p1 z1)))]) ~ ((z' ++ z1') ++ [msg (f (ostomsg (getelt_at_pos p1 z1')))]).
Ltac funcapp_f1m'_in g n H:= apply funcapp_f1m' with (f:=g) (p1:=n) in H; unfold getelt_at_pos in H; simpl in H.
Axiom ifmor_ifm: forall f b x y, (f (If b then x else y)) # (If b then (f x) else (f y)).
 Lemma extFuncapp1: forall n b b' x x' y y' (z z': mylist n) g, (z ++ [bol b, msg (If b then x else y)]) ~ (z' ++ [bol b', msg (If b' then x' else y')]) -> (z ++ [bol b, msg (If b then x else y), msg (If b then (g x) else |_)])~ (z' ++ [bol b', msg (If b' then x' else y'), msg (If b' then (g x') else |_)]).


                      Proof. intros.
                             
                             funcapp_f1m'_in g 2 H.
                             
                             simpl.
                             repeat rewrite ifmor_ifm in H.
funcapp_fm_last |_ H; auto.    apply ind_assoc in H; simpl in H.
       apply funcapp_f3bm' with (f:= (ifm_then_else_)) (p1:= 1) (p2:=3) (p3:=4) in H; unfold getelt_at_pos; simpl in H.
       simpl in H.
(********************)
     
       apply ind_assoc in H; simpl in H.
       
 do 2  apply restr with (p:= droplastsec) in H; unfold droplastsec in H; simpl in H; simpl; try rewrite Nat.eqb_refl; auto.
 repeat rewrite aply_ifeval_gen in H;auto. Qed.

                      Axiom eqm_cong: forall m1 m2 m3 m4, m1 # m2 -> m3 # m4 -> (eqm m1 m3) ## (eqm m2 m4).
Set Nested Proofs Allowed.
Add Parametric Morphism: (@ eqm) with
    signature EQm ==> EQm ==> EQb as eqm_mor.
Proof.    intros.  rewrite H, H0. reflexivity.  Qed.
Axiom orB_cong: forall b1 b2 b3 b4, b1 ## b2 -> b3 ## b4 -> (IF b1 then TRue else b3) ## (IF b2 then TRue else b4).
Add Parametric Morphism: (@orB) with
      signature EQb ==> EQb ==> EQb as orB_mor.
Proof. intros. apply orB_cong; auto.  Qed.           
Lemma rep_first_ballot: forall t t0 t1 : message,
      let v0 := V0 (N 0) in
      let v1 := V1 (N 0) in
      (| v0 |) #? (| v1 |) ## TRue ->
      Fresh [1; 2; 3; 4] [msg t, msg v0, msg v1, msg t0, msg t1] = true ->
      closMylist [msg t] = true ->
      (Datatypes.length (distMvars [msg t0, msg t1]) =? 2)%nat = true ->
      bVarMylist [msg t0, msg t1] = nil ->
      let mvl := [5; 6] in
      mVarMsg t0 = mvl /\ mVarMsg t1 = mvl ->
                
                 let r0 := (r 1) in
                 let r1 := (r 2) in
                 let k0 := (kc (N 3)) in
                 let k1 := (kc (N 4)) in
                 let c00 := (comm v0 k0) in
                 let c01 := (comm v0 k1) in
                 let c10 := (comm v1 k0) in
                 let c11 := (comm v1 k1) in
                 let b00 := (bl c00 t r0) in
                 let b11 := (bl c11 t r1) in
                 let b10 := (bl c10 t r0) in
                 let b01 := (bl c01 t r0) in
                 let t2 := ({{ 5 := (bl c00 t r0) }} ({{ 6:=(bl c11 t r1) }} t0)) in
                 let t3 := ({{ 5 := (bl c00 t r0) }} ({{ 6:=(bl c11 t r1) }} t1)) in
                 let t4 := ({{ 5 := (bl c10 t r0) }} ({{ 6:=(bl c01 t r1) }} t0)) in
                 let t5 := ({{ 5 := (bl c10 t r0) }} ({{ 6:=(bl c01 t r1) }} t1)) in
                 let e00 := (enc ((c00, ((ub c00 t r0 t2), (N 0))), TWO) (pke 11) (er 7)) in
                 let e11 := (enc ((c11, ((ub c11 t r1 t3), (N 1))), TWO) (pke 11) (er 8)) in
                 let e10 := (enc ((c10, ((ub c10 t r0 t4), (N 0))), TWO) (pke 11) (er 7)) in
                 let e01 := (enc ((c01, ((ub c01 t r1 t5), (N 1))), TWO) (pke 11) (er 8)) in
                 let pv00 := (c00, ((ub c00 t r0 t2), (N 0))) in
                 let pv11 := (c11, ((ub c11 t r1 t3), (N 1))) in
                 let pv10 := (c10, ((ub c10 t r0 t4), (N 0))) in
                 let pv01 := (c01, ((ub c01 t r1 t5), (N 1))) in
                 let phi02:= [msg b00, msg b11, msg e00, msg e11] in
                 let phi12:= [msg b10, msg b01, msg e10, msg e01] in
                 let fphi02:= f (toListm phi02) in
                
                 let s0 := (If (! (isin pv00 ((pi1 (d 1 fphi02)), ((pi1 (d 2 fphi02)), (pi1 (d 3 fphi02)))))) then (shufl (pi1 (d 1 fphi02)) (pi1 (d 2 fphi02)) (pi1 (d 3 fphi02))) else O)in
                                
                 let dv0 := (If (dist fphi02) & (pvchecks fphi02) then s0 else |_) in
                 let fphi12:= f (toListm phi12) in
                 let s1 := (If (! (isin pv10 ((pi1 (d 1 fphi12)), ((pi1 (d 2 fphi12)), (pi1 (d 3 fphi12)))))) then (shufl (pi1 (d 1 fphi12)) (pi1 (d 2 fphi12)) (pi1 (d 3 fphi12))) else O)in
                 let dv1 := (If (dist fphi12) & (pvchecks fphi12) then s1 else |_) in
                 let acc00 := (acc c00 t r0 t2) in
                 let acc11 := (acc c11 t r1 t3) in
                 let acc10 := (acc c10 t r0 t4) in
                 let acc01 := (acc c01 t r1 t5) in
                 let phi03:= phi02 ++[msg dv0] in
                 let phi13:= phi12 ++[msg dv1] in
                 let fphi03 := f (toListm phi03) in
                 let l00 := (If (bnlcheck c00 (N 0) fphi03) then (enc ((label c00 fphi03), (k0, THREE)) (pke 11) (er 9)) else O) in
                 let l11 := (If (bnlcheck c11 (N 1) fphi03) then (enc ((label c11 fphi03), (k1, THREE)) (pke 11) (er 10)) else O) in
                 let fphi13 := f (toListm phi13) in
                 let l10 := (If (bnlcheck c10 (N 0) fphi13) then (enc ((label c10 fphi13), (k0, THREE)) (pke 11) (er 9)) else O) in
                 let l01 := (If (bnlcheck c01 (N 1) fphi13) then (enc ((label c01 fphi13), (k1, THREE)) (pke 11) (er 10)) else O) in
                 let phi05:= phi03++[msg l00, msg l11] in   
                 let phi15:= phi13++[msg l10, msg l01] in
                 let fphi05 := f (toListm phi05) in
                 let fphi15 := f (toListm phi15) in
                 let do0 := (If (dist fphi05)& (pochecks fphi05)& (((isink k0 fphi05)&(isink k1 fphi05)) or (! ((isink k0 fphi05)or (isink k1 fphi05)))) then (sotrm fphi05) else |_) in
   let do1 := (If (dist fphi15)& (pochecks fphi15)& ((isink k0 fphi15)&(isink k1 fphi15)) (* or (! ((isink k0 fphi15)or (isink k1 fphi15)))) *) then (sotrm fphi15) else |_) in             
                 let t0s0 := (If acc00 & acc11 then ((e00, (e11, dv0)), (l00, (l11, do0))) else |_) in
                 let t1s1 := (If acc10 & acc01 then ((e10, (e01, dv1)), (l10, (l01, do1))) else |_) in
                 (occur_name_mylist 100 [msg t, msg t0, msg t1] = false) -> (Fresh (cons 0 nil) [msg t, msg t2, msg t3, msg t4, msg t5] = true) ->
                 [msg b00, msg b11, msg t0s0] ~ [msg b10, msg b01, msg t1s1].
           
Proof.            intros.
                      unfold t0s0, t1s1, l00, l10, bnlcheck.
                      (** x ~ y **)
                      (**x~ x' and y~y', x' ~ y' **)
                      (** replace the first voters' nonce (N 0) with a fresh nonce (N 20) **)

                      unfold do0, dv0.
                      unfold s0. unfold e00.
Axiom dummy: forall {n} (z z': mylist n), z ~ z'.
pose proof(dummy  [msg b00, msg b11,
   msg
     (If (acc00) & acc11
         then (e00,
              (e11,
              If (dist fphi02) & (pvchecks fphi02)
                 then If ! (isin pv00 (pi1 (d 1 fphi02), (pi1 (d 2 fphi02), pi1 (d 3 fphi02))))
                         then shufl (pi1 (d 1 fphi02)) (pi1 (d 2 fphi02)) (pi1 (d 3 fphi02)) 
                         else O 
                 else |_),
              (l00,
              (l11,
              If (dist fphi05) &
                 (pochecks fphi05) & ((isin k0 fphi05) & (isin k1 fphi05)) or ! ((isin k0 fphi05) or (isin k1 fphi05))
                 then sotrm fphi05 
                 else |_))) 
         else |_)] (let phi02' := [msg b00, msg b11, msg {(c00, (ub c00 t r0 t2, N 20), TWO) }_ 11 ^^ 7 , msg e11] in
                                          let fphi02':= f (toListm phi02') in
                                          let s0' := (If (! (isin pv00 ((pi1 (d 1 fphi02')), ((pi1 (d 2 fphi02')), (pi1 (d 3 fphi02')))))) then (shufl (pi1 (d 1 fphi02')) (pi1 (d 2 fphi02')) (pi1 (d 3 fphi02'))) else O) in
                                          let dv0' :=  (If (dist fphi02') & (pvchecks fphi02') then s0' else |_) in
                                          let phi03':= phi02' ++ [msg (shufl (pi1 (d 1 fphi02')) (pi1 (d 2 fphi02')) (pi1 (d 3 fphi02')))] in
                                          let fphi03':= f (toListm phi03') in
                                          let l00' := (If (bnlcheck c00 (N 0) fphi03') then (enc ((label c00 fphi03'), (k0, THREE)) (pke 11) (er 9)) else O) in
                                          let l11' := (If (bnlcheck c11 (N 1) fphi03') then (enc ((label c11 fphi03'), (k1, THREE)) (pke 11) (er 10)) else O) in
                                          let phi05':= phi03' ++ [msg l00', msg l11'] in
                                          let fphi05':= f (toListm phi05') in
                                          let do0' := (If (dist fphi05')& (pochecks fphi05')& (((isink k0 fphi05')&(isink k1 fphi05')) or (! ((isink k0 fphi05')or (isink k1 fphi05')))) then (sotrm fphi05') else |_) in
                                          [msg b00, msg b11, msg (If (acc00) & acc11 then ( (enc (c00, (ub c00 t r0 t2, N 20), TWO) (pke 11) (er 9)) , (e11, dv0'), (l00', (l11', do0'))) else |_)])).
 unfold e10.
assert( (let phi02' :=
          [msg b00, msg b11,
          msg {(c00, (ub c00 t r0 t2, N 20), TWO) }_ 11 ^^ 7, 
          msg e11] in
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
        let phi03' :=
          phi02' ++
          [msg
             (shufl (pi1 (d 1 fphi02')) (pi1 (d 2 fphi02'))
                (pi1 (d 3 fphi02')))] in
        let fphi03' := f (toListm phi03') in
        let l00' :=
          If bnlcheck c00 (N 0) fphi03'
             then (enc (label c00 fphi03', (k0, THREE)) (pke 11) (er 9)) 
             else O in
        let l11' :=
          If bnlcheck c11 (N 1) fphi03'
             then (enc (label c11 fphi03', (k1, THREE)) (pke 11) (er 10)) 
             else O in
        let phi05' := phi03' ++ [msg l00', msg l11'] in
        let fphi05' := f (toListm phi05') in
        let do0' :=
          If (dist fphi05') &
             (pochecks fphi05') &
             ((isink k0 fphi05') & (isink k1 fphi05')) (*or
             ! ((isink k0 fphi05') or (isink k1 fphi05')) *)
             then sotrm fphi05' 
             else |_ in
        [msg b00, msg b11,
        msg
          (If (acc00) & acc11
              then ((enc (c00, (ub c00 t r0 t2, N 20), TWO) (pke 11) (er 9)),
                   (e11, dv0'), (l00', (l11', do0'))) 
           else |_)]) ~


                      (let phi12' :=
          [msg b10, msg b01,
          msg {(c10, (ub c10 t r0 t4, N 20), TWO) }_ 11 ^^ 7, 
          msg e01] in
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
        let phi13' :=
          phi12' ++
          [msg
             (shufl (pi1 (d 1 fphi12')) (pi1 (d 2 fphi12'))
                (pi1 (d 3 fphi12')))] in
        let fphi13' := f (toListm phi13') in
        let l10' :=
          If bnlcheck c10 (N 0) fphi13'
             then (enc (label c10 fphi13', (k0, THREE)) (pke 11) (er 9)) 
             else O in
        let l01' :=
          If bnlcheck c10 (N 1) fphi13'
             then (enc (label c10 fphi13', (k1, THREE)) (pke 11) (er 10)) 
             else O in
        let phi15' := phi13' ++ [msg l10', msg l01'] in
        let fphi15' := f (toListm phi15') in
        let do1' :=
          If (dist fphi15') &
             (pochecks fphi15') &
             ((isink k0 fphi15') & (isink k1 fphi15')) (* or
             ! ((isink k0 fphi15') or (isink k1 fphi15')) *)
             then sotrm fphi15' 
             else |_ in
        [msg b10, msg b01,
        msg
          (If (acc10) & acc01
              then ((enc (c10, (ub c10 t r0 t4, N 20), TWO) (pke 11) (er 9)),
                   (e01, dv1'), (l10', (l01', do1'))) 
           else |_)])).
simpl.
assert( (ncheck (N 0) (f
                                 [b10; b01; (enc (c10, (ub c10 t r0 t4, N 20), TWO) (pke 11) (er 7)); e01;
                                 shufl (pi1 (d 1 (f [b10; b01; (enc (c10, (ub c10 t r0 t4, N 20), TWO) (pke 11) (er 7)); e01])))
                                   (pi1 (d 2 (f [b10; b01; (enc (c10, (ub c10 t r0 t4, N 20), TWO) (pke 11) (er 7)); e01])))
                                   (pi1 (d 3 (f [b10; b01; (enc (c10, (ub c10 t r0 t4, N 20), TWO) (pke 11) (er 7)); e01])))])) ## FAlse).
unfold ncheck. 
unfold isin. 

Lemma tau1: forall x y z, (tau 1 (x, (y, z))) # x.
Proof. intros. unfold tau. rewrite proj1; auto. reflexivity.
Qed.
Lemma tau2: forall x y z, (tau 2 (x, (y, z))) # y.
Proof. intros. unfold tau; rewrite proj2, proj1;auto. reflexivity. Qed.
Lemma tau3: forall x y z, (tau 3 (x, (y, z))) # z.
Proof. intros. unfold tau. repeat rewrite proj2; try reflexivity.
Qed.
Eval compute in FAlse or TRue.
rewrite tau1, tau2, tau3.
Axiom freshneq: forall (n : nat) (m : message),
       ^? (m) = true  -> Fresh (cons n nil) [msg m] = true ->
       ([bol (N n) #? m]) ~ [bol FAlse].
simpl.
pose proof(freshneq 0 (pi2
      (pi2
         (pi2
            (pi1
               (f
                  [b10; b01; (enc (c10, (ub c10 t r0 t4, N 20), TWO) (pke 11) (er 7));
                  e01;
                  shufl
                    (pi1
                       (d 1
                          (f
                             [b10; b01;
                             (enc (c10, (ub c10 t r0 t4, N 20), TWO) (pke 11) (er 7));
                             e01])))
                    (pi1
                       (d 2
                          (f
                             [b10; b01;
                             (enc (c10, (ub c10 t r0 t4, N 20), TWO) (pke 11) (er 7));
                             e01])))
                    (pi1
                       (d 3
                          (f
                             [b10; b01;
                             (enc (c10, (ub c10 t r0 t4, N 20), TWO) (pke 11) (er 7));
                             e01])))])))))). 
simpl in H8.

simpl in H1. rewrite andb_true_iff in H1. inversion H1.
repeat rewrite H9 in H8. 
unfold t4, t5 in H8.
 rewrite  clos_sub_vtrm in H8;auto.
 rewrite  clos_sub_vtrm in H8;auto.
repeat rewrite andb_true_r, andb_true_l in H8.
 unfold Fresh in H8, H6.  simpl in H8, H6.
 (** ********)
 assert( occur_name_msg 0 t = false).
destruct (occur_name_msg 0 t). simpl in H6.
inversion H6. reflexivity.
assert( occur_name_msg 0 t2 = false).
destruct (occur_name_msg 0 t2).
simpl in H6. rewrite H11 in H6. simpl in H6. inversion H6. reflexivity.
assert( occur_name_msg 0 t3 = false).
destruct (occur_name_msg 0 t3).
simpl in H6. rewrite H12 in H6. simpl in H6. inversion H6. rewrite H11. reflexivity. reflexivity.
assert( occur_name_msg 0 t4 = false).
destruct (occur_name_msg 0 t4).
simpl in H6. rewrite H11, H12, H13 in H6. simpl in H6. inversion H6. reflexivity.
assert( occur_name_msg 0 t5 = false).
destruct (occur_name_msg 0 t5).
simpl in H6. rewrite H11, H12, H13, H14 in H6. simpl in H6. inversion H6. reflexivity.
fold t4 in H8.
rewrite H11, H14, H15 in H8. simpl in H8.
Axiom consteql: forall x f, const_bol f = true -> [bol x]~[bol f] -> x ## f.
assert( (const_bol FAlse) = true). reflexivity.
apply consteql in H8; auto.
rewrite H8. 
(** prove N0 is fresh in tau2 of the decrypted message **)


pose proof(freshneq 0 (pi2
      (pi2
         (pi2
            (pi1
               (pi2 (f
                  [b10; b01; (enc (c10, (ub c10 t r0 t4, N 20), TWO) (pke 11) (er 7));
                  e01;
                  shufl
                    (pi1
                       (d 1
                          (f
                             [b10; b01;
                             (enc (c10, (ub c10 t r0 t4, N 20), TWO) (pke 11) (er 7));
                             e01])))
                    (pi1
                       (d 2
                          (f
                             [b10; b01;
                             (enc (c10, (ub c10 t r0 t4, N 20), TWO) (pke 11) (er 7));
                             e01])))
                    (pi1
                       (d 3
                          (f
                             [b10; b01;
                             (enc (c10, (ub c10 t r0 t4, N 20), TWO) (pke 11) (er 7));
                             e01])))]))))))). 
simpl in H17.

repeat rewrite H9 in H17. 
unfold t4, t5 in H17.
 rewrite  clos_sub_vtrm in H17;auto.
 rewrite  clos_sub_vtrm in H17;auto. simpl in H17.
 unfold Fresh in H17; simpl in H17.
 fold t4 in H17.
 rewrite H11, H14, H15 in H17. simpl in H17.



apply consteql in H17; auto.
rewrite H17. 
clear H8 H17.

pose proof(freshneq 0 (pi2 (pi2 (pi2 (pi2 (pi2 (f
                  [b10; b01; (enc (c10, (ub c10 t r0 t4, N 20), TWO) (pke 11) (er 7));
                  e01;
                  shufl
                    (pi1
                       (d 1
                          (f
                             [b10; b01;
                             (enc (c10, (ub c10 t r0 t4, N 20), TWO) (pke 11) (er 7));
                             e01])))
                    (pi1
                       (d 2
                          (f
                             [b10; b01;
                             (enc (c10, (ub c10 t r0 t4, N 20), TWO) (pke 11) (er 7));
                             e01])))
                    (pi1
                       (d 3
                          (f
                             [b10; b01;
                             (enc (c10, (ub c10 t r0 t4, N 20), TWO) (pke 11) (er 7));
                             e01])))]))))))).
simpl in H8.
unfold t4, t5 in H8.
 rewrite  clos_sub_vtrm in H8;auto.
 rewrite  clos_sub_vtrm in H8;auto. simpl in H8.
repeat rewrite H9 in H8. simpl in H8.
unfold Fresh in H8; simpl in H8.
fold t4 in H8.
rewrite H11, H14, H15 in H8. simpl in H8.
apply consteql in H8; auto.
rewrite H8; clear H8; auto.
unfold orB.
 repeat rewrite IFFALSE_B. reflexivity. 
  (left;inversion H4; unfold distMvars; simpl; try rewrite H17; try rewrite H18; try reflexivity). 
(left;inversion H4; unfold distMvars; simpl; try rewrite H17; try rewrite H18; try rewrite H19; try reflexivity). 
(left;inversion H4; unfold distMvars; simpl; try rewrite H17; try rewrite H18; try rewrite H19; try reflexivity). 
(left;inversion H4; unfold distMvars; simpl; try rewrite H17; try rewrite H18; try rewrite H19; try reflexivity). 
(left;inversion H4; unfold distMvars; simpl; try rewrite H17; try rewrite H18; try rewrite H19; try rewrite H11; try rewrite H12; try reflexivity).
(left;inversion H4; unfold distMvars; simpl; try rewrite H17; try rewrite H18; try rewrite H19; try rewrite H11; try rewrite H12; try reflexivity).

(*******************************************)
assert( let x:= (enc (c10, (ub c10 t r0 t4, N 20), TWO) (pke 11) (er 7)) in (bnlcheck c10 (N 0)
                  (f
                     [b10; b01; x; e01;
                     shufl (pi1 (d 1 (f [b10; b01; x; e01])))
                       (pi1 (d 2 (f [b10; b01; x; e01])))
                       (pi1 (d 3 (f [b10; b01; x; e01])))])) ## FAlse).
simpl. unfold bnlcheck.
rewrite H8. repeat rewrite andB_FAlse_r; try reflexivity.
rewrite H9.
rewrite IFFALSE_M.
clear H8 H9.
(********************************************)

assert( let x:= (enc (c00, (ub c00 t r0 t2, N 20), TWO) (pke 11) (er 7)) in  (bnlcheck c00 (N 0)
                    (f
                       [b00; b11; x; e11;
                       shufl (pi1 (d 1 (f [b00; b11; x; e11])))
                         (pi1 (d 2 (f [b00; b11; x; e11])))
                         (pi1 (d 3 (f [b00; b11; x; e11])))])) ## FAlse).
 unfold bnlcheck.
unfold ncheck. unfold isin.
rewrite tau1, tau2, tau3.
pose proof( freshneq 0 (let x:= (enc (c00, (ub c00 t r0 t2, N 20), TWO) (pke 11) (er 7)) in (tau 3 (pi2 (tau 1 (f
                       [b00; b11; x; e11;
                       shufl (pi1 (d 1 (f [b00; b11; x; e11])))
                         (pi1 (d 2 (f [b00; b11; x; e11])))
                         (pi1 (d 3 (f [b00; b11; x; e11])))])))))).
simpl in H8.
unfold t2, t3 in H8.
 rewrite  clos_sub_vtrm in H8;auto.
 rewrite  clos_sub_vtrm in H8;auto. simpl in H8.
simpl in H1.
simpl in H1. rewrite andb_true_iff in H1. inversion H1.
repeat rewrite H9 in H8.
simpl in H8.
unfold Fresh in H8, H6; simpl in H8, H6.
assert( occur_name_msg 0 t = false). 
destruct (occur_name_msg 0 t). simpl in H6.
inversion H6. reflexivity.
assert( occur_name_msg 0 t2 = false).
destruct (occur_name_msg 0 t2).
simpl in H6. rewrite H11 in H6. simpl in H6. inversion H6. reflexivity.
assert( occur_name_msg 0 t3 = false).
destruct (occur_name_msg 0 t3).
simpl in H6. rewrite H12 in H6. simpl in H6. inversion H6. rewrite H11. reflexivity. reflexivity.
fold t2 in H8.
rewrite H11, H12, H13 in H8. simpl in H8. 
apply consteql in H8; auto; try  (left;inversion H4; unfold distMvars; simpl; try rewrite H16; try rewrite H17; try rewrite H18; try rewrite H19; try reflexivity).
Axiom extcomphid: forall {n} (z z': mylist n), z ~ z'.
(******)
pose proof( freshneq 0 (let x:= (enc (c00, (ub c00 t r0 t2, N 20), TWO) (pke 11) (er 7)) in (tau 3 (pi2 (tau 2 (f
                       [b00; b11; x; e11;
                       shufl (pi1 (d 1 (f [b00; b11; x; e11])))
                             (pi1 (d 2 (f [b00; b11; x; e11])))
                             (pi1 (d 3 (f [b00; b11; x; e11])))])))))).
simpl in H14.                         
rewrite H9 in H14.
unfold t2, t3 in H14.
 rewrite  clos_sub_vtrm in H14;auto.
 rewrite  clos_sub_vtrm in H14;auto. simpl in H14.
unfold Fresh in H14. simpl in H14.
fold t2 in H14.
rewrite H11, H12, H13 in H14. simpl in H14.
apply consteql in H14; auto; try (left;inversion H4; unfold distMvars; simpl; try rewrite H16; try rewrite H17; try rewrite H18; try rewrite H19; try reflexivity).
(*******************************)
pose proof(freshneq 0 (let x:= (enc (c00, (ub c00 t r0 t2, N 20), TWO) (pke 11) (er 7)) in (tau 3 (pi2 (tau 3 (f
                       [b00; b11; x; e11;
                       shufl (pi1 (d 1 (f [b00; b11; x; e11])))
                             (pi1 (d 2 (f [b00; b11; x; e11])))
                             (pi1 (d 3 (f [b00; b11; x; e11])))])))))).
simpl in H15.
rewrite H9 in H15.
unfold t2, t3 in H15.
 rewrite  clos_sub_vtrm in H15;auto.
 rewrite  clos_sub_vtrm in H15;auto. simpl in H15.
unfold Fresh in H15, H6. simpl in H15, H6.
fold t2 in H15.
rewrite H11, H12, H13 in H15. simpl in H15.
apply consteql in H15; auto; try (left; try inversion H4; unfold distMvars; simpl; try rewrite H16; try rewrite H17; try reflexivity).
rewrite H8, H14, H15. unfold orB. repeat rewrite IFFALSE_B. simpl.
repeat rewrite andB_FAlse_r; try reflexivity.
(left;inversion H4; unfold distMvars; simpl; try rewrite H16; try rewrite H17; try rewrite H18; try rewrite H19; try reflexivity). 
(left;inversion H4; unfold distMvars; simpl; try rewrite H16;  try rewrite H17; try rewrite H18; try rewrite H19; try reflexivity).
(left;inversion H4; unfold distMvars; simpl; try rewrite H16;  try rewrite H17; try rewrite H18; try rewrite H19; try reflexivity). 
(left;inversion H4; unfold distMvars; simpl; try rewrite H15;  try rewrite H16; try rewrite H18; try rewrite H19; try reflexivity).
(left;inversion H4; unfold distMvars; simpl; try rewrite H9;  try rewrite H10; try rewrite H17; try rewrite H18; try rewrite H19; try reflexivity).
(left;inversion H4; unfold distMvars; simpl; try rewrite H9;  try rewrite H10; try rewrite H17; try rewrite H18; try rewrite H19; try reflexivity). rewrite H8.
rewrite IFFALSE_M.
unfold isink.
unfold k0.
(** we need to prove that the attacker cannot compute the commitment key **)
pose proof (ENCCCA2).
Axiom infeasible_comp_ck: forall n t g, (closMsg t) = true ->
                                          (** (distMvars [msg t']) = (cons m nil) ->  I can prove this:Fresh (cons n nil) [msg t, msg t'] = true **) ((g t) #? (kc (N n)))  ## FAlse.
(*** I will prove this later **) unfold b00.
Eval compute in b00.
Axiom eqm_sym: forall m1 m2, (m1 #? m2) ## (m2 #? m1).
 repeat rewrite eqm_sym with (m1:= (kc (N 3))).
repeat rewrite infeasible_comp_ck with (n:= 3); auto.
unfold orB. 
repeat rewrite IFFALSE_B.
repeat rewrite andB_FAlse_l.  repeat rewrite andB_FAlse_r. repeat rewrite IFFALSE_M. simpl.
(** we replace the encryption that emits *)


pose proof(compHid_ext).
apply extcomphid.
 
 simpl.
simpl in H1;
rewrite andb_true_iff in H1;
inversion H1;
rewrite H10; unfold t4, t5; repeat rewrite clos_sub_vtrm;try left; inversion H4; unfold distMvars; simpl; try rewrite H12; try rewrite H13; try reflexivity.

simpl.
simpl in H1;
rewrite andb_true_iff in H1;
inversion H1;
rewrite H10; unfold t4, t5; repeat rewrite clos_sub_vtrm;try left; inversion H4; unfold distMvars; simpl; try rewrite H12; try rewrite H13; try reflexivity.

simpl.
simpl in H1;
rewrite andb_true_iff in H1;
inversion H1;
rewrite H10; unfold t4, t5; repeat rewrite clos_sub_vtrm;try left; inversion H4; unfold distMvars; simpl; try rewrite H12; try rewrite H13; try reflexivity.


simpl. 
simpl in H1;
rewrite andb_true_iff in H1;
inversion H1;
rewrite H10; unfold t2, t3; repeat rewrite clos_sub_vtrm;try left; inversion H4; unfold distMvars; simpl; try rewrite H12; try rewrite H13; try reflexivity.



simpl.
simpl in H1;
rewrite andb_true_iff in H1;
inversion H1;
rewrite H10; unfold t2, t3; repeat rewrite clos_sub_vtrm;try left; inversion H4; unfold distMvars; simpl; try rewrite H12; try rewrite H13; try reflexivity.

simpl.
simpl in H1;
rewrite andb_true_iff in H1;
inversion H1;
rewrite H10; unfold t2, t3; repeat rewrite clos_sub_vtrm;try left; inversion H4; unfold distMvars; simpl; try rewrite H12; try rewrite H13; try reflexivity.
apply extcomphid.
Qed.
End lemma148.
