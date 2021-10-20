
Require Export prop_13.
(** * Extending Blindness axiom *)
Proposition Prop_21:  forall (t t0 t1 : message), let v0 := (V0 (nonce 0)) in
                                                                                                      let v1 := (V1 (nonce 0)) in
                                                                                                      (|v0|#?|v1|) ## TRue ->  (Fresh (cons 1 (cons 2 (cons 3 (cons 4 nil)))) ([msg t, msg v0, msg v1, msg t0, msg t1])  = true) ->  closMylist ([msg t]) = true -> ((length (distMvars [msg t0, msg t1]))=?  2)%nat = true -> bVarMylist [msg t0, msg t1] = nil  ->
    let mvl:= (cons 5 (cons 6 nil)) in  (mVarMsg t0) = mvl /\ (mVarMsg t1) = mvl ->
                 let r0 := (r 1) in
                 let r1 := (r 2) in
                 let k0 := (kc (nonce 3)) in
                 let k1 := (kc (nonce 4)) in
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
apply split_fresh with (l1:= cons 1 (cons 2 nil))(l2:= cons 3 (cons 4 nil)) in H0.
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
apply split_fresh with (l1:= cons 1 (cons 2 nil)) in H5.
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
pose proof(extFreshInd 4 100 0 [msg (bl (comm v1 (kc (Mvar 0))) t (r 1)), msg (bl (comm v0 (kc (nonce 3))) t (r 2)),
       bol
         (acc (comm v1 (kc (Mvar 0))) t (r 1)
            {{5 := bl (comm v1 (kc (Mvar 0))) t (r 1)}} ({{6 := bl (comm v0 (kc (nonce 3))) t (r 2)}} (t0))) &
         (acc (comm v0 (kc (nonce 3))) t (r 2)
            {{5 := bl (comm v1 (kc (Mvar 0))) t (r 1)}} ({{6 := bl (comm v0 (kc (nonce 3))) t (r 2)}} (t1))),
       msg
         (If (acc (comm v1 (kc (Mvar 0))) t (r 1)
                {{5 := bl (comm v1 (kc (Mvar 0))) t (r 1)}} ({{6 := bl (comm v0 (kc (nonce 3))) t (r 2)}} (t0))) &
             (acc (comm v0 (kc (nonce 3))) t (r 2)
                {{5 := bl (comm v1 (kc (Mvar 0))) t (r 1)}} ({{6 := bl (comm v0 (kc (nonce 3))) t (r 2)}} (t1)))
             then (ub (comm v0 (kc (nonce 3))) t (r 2)
                     {{5 := bl (comm v1 (kc (Mvar 0))) t (r 1)}} ({{6 := bl (comm v0 (kc (nonce 3))) t (r 2)}} (t1)),
                  (comm v0 (kc (nonce 3)), kc (nonce 3)),
                  (ub (comm v1 (kc (Mvar 0))) t (r 1)
                     {{5 := bl (comm v1 (kc (Mvar 0))) t (r 1)}} ({{6 := bl (comm v0 (kc (nonce 3))) t (r 2)}} (t0)),
                  (comm v1 (kc (Mvar 0)), kc (Mvar 0))))
             else (|_, (comm v0 (kc (nonce 3)), kc (nonce 3)), (|_, (comm v1 (kc (Mvar 0)), kc (Mvar 0)))))]).
simpl in H6.


repeat  rewrite sub_in_sub with (n1:=0) (t:= ({{6 := bl (comm v0 (kc (nonce 3))) t (r 2)}} (t1))) in H6.
repeat  rewrite sub_in_sub with (n1:=0) (t:= t1) in H6.
simpl in H6.
do 2 rewrite sub_clos with (n:=0)(t:=t) in H6; simpl in H1; try rewrite Bool.andb_true_r in H1; eauto.
inversion H4.
do 2 rewrite sub_ident with (n:=0) (t:= t1) in H6;  try rewrite H7; try rewrite H8;auto.

repeat  rewrite sub_in_sub with (n1:=0) (t:= ({{6 := bl (comm v0 (kc (nonce 3))) t (r 2)}} (t0))) in H6.
repeat  rewrite sub_in_sub with (n1:=0) (t:= t0) in H6.  simpl in H6.
do 2 rewrite sub_ident with (n:=0) (t:= t0) in H6;  try rewrite H7; try rewrite H8;auto.

simpl in H6.
do 2 rewrite sub_clos with (n:=0)(t:=t) in H6; simpl in H1; try rewrite Bool.andb_true_r in H1; eauto.

(** then replace n3 with n4 *)

pose proof (extFreshInd 3 4 0
[msg (bl (comm (V1 (nonce 0)) (kc (nonce 100))) t (rb (nonce 1))), msg (bl (comm (V0 (nonce 0)) (kc (Mvar 0))) t (rb (nonce 2))),
       bol
         (IF acc (comm (V1 (nonce 0)) (kc (nonce 100))) t (rb (nonce 1))
               {{5
               := bl (comm (V1 (nonce 0)) (kc (nonce 100))) t (rb (nonce 1))}} ({{6
                                                                    := bl (comm (V0 (nonce 0)) (kc (Mvar 0))) t (rb (nonce 2))}}
                                                                    (t0))
          then acc (comm (V0 (nonce 0)) (kc (Mvar 0))) t (rb (nonce 2))
                 {{5
                 := bl (comm (V1 (nonce 0)) (kc (nonce 100))) t (rb (nonce 1))}} ({{6
                                                                      := bl (comm (V0 (nonce 0)) (kc (Mvar 0))) t (rb (nonce 2))}}
                                                                      (t1)) else FAlse),
       msg
         (If IF acc (comm (V1 (nonce 0)) (kc (nonce 100))) t (rb (nonce 1))
                  {{5
                  := bl (comm (V1 (nonce 0)) (kc (nonce 100))) t (rb (nonce 1))}} ({{6
                                                                       := bl (comm (V0 (nonce 0)) (kc (Mvar 0))) t (rb (nonce 2))}}
                                                                       (t0))
             then acc (comm (V0 (nonce 0)) (kc (Mvar 0))) t (rb (nonce 2))
                    {{5
                    := bl (comm (V1 (nonce 0)) (kc (nonce 100))) t (rb (nonce 1))}} ({{6
                                                                         := bl (comm (V0 (nonce 0)) (kc (Mvar 0))) t (rb (nonce 2))}}
                                                                         (t1)) else FAlse
             then (ub (comm (V0 (nonce 0)) (kc (Mvar 0))) t (rb (nonce 2))
                     {{5
                     := bl (comm (V1 (nonce 0)) (kc (nonce 100))) t (rb (nonce 1))}} ({{6
                                                                          := bl (comm (V0 (nonce 0)) (kc (Mvar 0))) t
                                                                               (rb (nonce 2))}}
                                                                          (t1)), (comm (V0 (nonce 0)) (kc (Mvar 0)), kc (Mvar 0)),
                  (ub (comm (V1 (nonce 0)) (kc (nonce 100))) t (rb (nonce 1))
                     {{5
                     := bl (comm (V1 (nonce 0)) (kc (nonce 100))) t (rb (nonce 1))}} ({{6
                                                                          := bl (comm (V0 (nonce 0)) (kc (Mvar 0))) t
                                                                               (rb (nonce 2))}}
                                                                          (t0)),
                  (comm (V1 (nonce 0)) (kc (nonce 100)), kc (nonce 100))))
             else (|_, (comm (V0 (nonce 0)) (kc (Mvar 0)), kc (Mvar 0)), (|_, (comm (V1 (nonce 0)) (kc (nonce 100)), kc (nonce 100)))))]).
simpl in H9.


repeat  rewrite sub_in_sub with (n1:=0) (t:= ({{6:= bl (comm (V0 (nonce 0)) (kc (Mvar 0))) t (rb (nonce 2))}} t1)) in H9.
repeat  rewrite sub_in_sub with (n1:=0) (t:= t1) in H9.
simpl in H9.
do 2 rewrite sub_clos with (n:=0)(t:=t) in H9; simpl in H1; try rewrite Bool.andb_true_r in H1; eauto.
inversion H4.
do 2 rewrite sub_ident with (n:=0) (t:= t1) in H9;  try rewrite H7; try rewrite H8;auto.

repeat  rewrite sub_in_sub with (n1:=0) (t:= ({{6 := bl (comm (V0 (nonce 0)) (kc (Mvar 0))) t (rb (nonce 2))}} t0))  in H9.
repeat  rewrite sub_in_sub with (n1:=0) (t:= t0) in H9.  simpl in H9.
do 2 rewrite sub_ident with (n:=0) (t:= t0) in H9;  try rewrite H7; try rewrite H8;auto.

simpl in H9.
do 2 rewrite sub_clos with (n:=0)(t:=t) in H9; simpl in H1; try rewrite Bool.andb_true_r in H1; eauto.


(** Finally, replace n100 with n3 *)

pose proof ( extFreshInd 100 3 0 [msg (bl (comm (V1 (nonce 0)) (kc (Mvar 0))) t (rb (nonce 1))), msg (bl (comm (V0 (nonce 0)) (kc (nonce 4))) t (rb (nonce 2))),
       bol
         (IF acc (comm (V1 (nonce 0)) (kc (Mvar 0))) t (rb (nonce 1))
               {{5
               := bl (comm (V1 (nonce 0)) (kc (Mvar 0))) t (rb (nonce 1))}} ({{6
                                                                    := bl (comm (V0 (nonce 0)) (kc (nonce 4))) t (rb (nonce 2))}}
                                                                    (t0))
          then acc (comm (V0 (nonce 0)) (kc (nonce 4))) t (rb (nonce 2))
                 {{5
                 := bl (comm (V1 (nonce 0)) (kc (Mvar 0))) t (rb (nonce 1))}} ({{6
                                                                      := bl (comm (V0 (nonce 0)) (kc (nonce 4))) t (rb (nonce 2))}}
                                                                      (t1)) else FAlse),
       msg
         (If IF acc (comm (V1 (nonce 0)) (kc (Mvar 0))) t (rb (nonce 1))
                  {{5
                  := bl (comm (V1 (nonce 0)) (kc (Mvar 0))) t (rb (nonce 1))}} ({{6
                                                                       := bl (comm (V0 (nonce 0)) (kc (nonce 4))) t (rb (nonce 2))}}
                                                                       (t0))
             then acc (comm (V0 (nonce 0)) (kc (nonce 4))) t (rb (nonce 2))
                    {{5
                    := bl (comm (V1 (nonce 0)) (kc (Mvar 0))) t (rb (nonce 1))}} ({{6
                                                                         := bl (comm (V0 (nonce 0)) (kc (nonce 4))) t (rb (nonce 2))}}
                                                                         (t1)) else FAlse
             then (ub (comm (V0 (nonce 0)) (kc (nonce 4))) t (rb (nonce 2))
                     {{5
                     := bl (comm (V1 (nonce 0)) (kc (Mvar 0))) t (rb (nonce 1))}} ({{6
                                                                          := bl (comm (V0 (nonce 0)) (kc (nonce 4))) t
                                                                               (rb (nonce 2))}}
                                                                          (t1)), (comm (V0 (nonce 0)) (kc (nonce 4)), kc (nonce 4)),
                  (ub (comm (V1 (nonce 0)) (kc (Mvar 0))) t (rb (nonce 1))
                     {{5
                     := bl (comm (V1 (nonce 0)) (kc (Mvar 0))) t (rb (nonce 1))}} ({{6
                                                                          := bl (comm (V0 (nonce 0)) (kc (nonce 4))) t
                                                                               (rb (nonce 2))}}
                                                                          (t0)),
                  (comm (V1 (nonce 0)) (kc (Mvar 0)), kc (Mvar 0))))
             else (|_, (comm (V0 (nonce 0)) (kc (nonce 4)), kc (nonce 4)), (|_, (comm (V1 (nonce 0)) (kc (Mvar 0)), kc (Mvar 0)))))]).
simpl in H12.


repeat  rewrite sub_in_sub with (n1:=0) (t:= ({{6:= bl (comm (V0 (nonce 0)) (kc (nonce 4))) t (rb (nonce 2))}} t1)) in H12.
repeat  rewrite sub_in_sub with (n1:=0) (t:= t1) in H12.
simpl in H12.
do 2 rewrite sub_clos with (n:=0)(t:=t) in H12; simpl in H1; try rewrite Bool.andb_true_r in H1; eauto.

do 2 rewrite sub_ident with (n:=0) (t:= t1) in H12;  try rewrite H7; try rewrite H8;auto.

repeat  rewrite sub_in_sub with (n1:=0) (t:= ({{6 := bl (comm (V0 (nonce 0)) (kc (nonce 4))) t (rb (nonce 2))}} t0))  in H12.
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
             else (|_, (c00, k0), (|_, (c11, k1))))]) (l3:= [msg (bl (comm (V1 (nonce 0)) (kc (nonce 100))) t (rb (nonce 1))), msg (bl (comm (V0 (nonce 0)) (kc (nonce 3))) t (rb (nonce 2))),
       bol
         (IF acc (comm (V1 (nonce 0)) (kc (nonce 100))) t (rb (nonce 1))
               {{5
               := bl (comm (V1 (nonce 0)) (kc (nonce 100))) t (rb (nonce 1))}} ({{6
                                                                    := bl (comm (V0 (nonce 0)) (kc (nonce 3))) t (rb (nonce 2))}}
                                                                    (t0))
          then acc (comm (V0 (nonce 0)) (kc (nonce 3))) t (rb (nonce 2))
                 {{5
                 := bl (comm (V1 (nonce 0)) (kc (nonce 100))) t (rb (nonce 1))}} ({{6
                                                                      := bl (comm (V0 (nonce 0)) (kc (nonce 3))) t (rb (nonce 2))}}
                                                                      (t1)) else FAlse),
       msg
         (If IF acc (comm (V1 (nonce 0)) (kc (nonce 100))) t (rb (nonce 1))
                  {{5
                  := bl (comm (V1 (nonce 0)) (kc (nonce 100))) t (rb (nonce 1))}} ({{6
                                                                       := bl (comm (V0 (nonce 0)) (kc (nonce 3))) t (rb (nonce 2))}}
                                                                       (t0))
             then acc (comm (V0 (nonce 0)) (kc (nonce 3))) t (rb (nonce 2))
                    {{5
                    := bl (comm (V1 (nonce 0)) (kc (nonce 100))) t (rb (nonce 1))}} ({{6
                                                                         := bl (comm (V0 (nonce 0)) (kc (nonce 3))) t (rb (nonce 2))}}
                                                                         (t1)) else FAlse
             then (ub (comm (V0 (nonce 0)) (kc (nonce 3))) t (rb (nonce 2))
                     {{5
                     := bl (comm (V1 (nonce 0)) (kc (nonce 100))) t (rb (nonce 1))}} ({{6
                                                                          := bl (comm (V0 (nonce 0)) (kc (nonce 3))) t
                                                                               (rb (nonce 2))}}
                                                                          (t1)), (comm (V0 (nonce 0)) (kc (nonce 3)), kc (nonce 3)),
                  (ub (comm (V1 (nonce 0)) (kc (nonce 100))) t (rb (nonce 1))
                     {{5
                     := bl (comm (V1 (nonce 0)) (kc (nonce 100))) t (rb (nonce 1))}} ({{6
                                                                          := bl (comm (V0 (nonce 0)) (kc (nonce 3))) t
                                                                               (rb (nonce 2))}}
                                                                          (t0)),
                  (comm (V1 (nonce 0)) (kc (nonce 100)), kc (nonce 100))))
             else (|_, (comm (V0 (nonce 0)) (kc (nonce 3)), kc (nonce 3)), (|_, (comm (V1 (nonce 0)) (kc (nonce 100)), kc (nonce 100)))))]) (l4:= [msg (bl (comm (V1 (nonce 0)) (kc (nonce 100))) t (rb (nonce 1))), msg (bl (comm (V0 (nonce 0)) (kc (nonce 4))) t (rb (nonce 2))),
       bol
         (IF acc (comm (V1 (nonce 0)) (kc (nonce 100))) t (rb (nonce 1))
               {{5
               := bl (comm (V1 (nonce 0)) (kc (nonce 100))) t (rb (nonce 1))}} ({{6
                                                                    := bl (comm (V0 (nonce 0)) (kc (nonce 4))) t (rb (nonce 2))}}
                                                                    (t0))
          then acc (comm (V0 (nonce 0)) (kc (nonce 4))) t (rb (nonce 2))
                 {{5
                 := bl (comm (V1 (nonce 0)) (kc (nonce 100))) t (rb (nonce 1))}} ({{6
                                                                      := bl (comm (V0 (nonce 0)) (kc (nonce 4))) t (rb (nonce 2))}}
                                                                      (t1)) else FAlse),
       msg
         (If IF acc (comm (V1 (nonce 0)) (kc (nonce 100))) t (rb (nonce 1))
                  {{5
                  := bl (comm (V1 (nonce 0)) (kc (nonce 100))) t (rb (nonce 1))}} ({{6
                                                                       := bl (comm (V0 (nonce 0)) (kc (nonce 4))) t (rb (nonce 2))}}
                                                                       (t0))
             then acc (comm (V0 (nonce 0)) (kc (nonce 4))) t (rb (nonce 2))
                    {{5
                    := bl (comm (V1 (nonce 0)) (kc (nonce 100))) t (rb (nonce 1))}} ({{6
                                                                         := bl (comm (V0 (nonce 0)) (kc (nonce 4))) t (rb (nonce 2))}}
                                                                         (t1)) else FAlse
             then (ub (comm (V0 (nonce 0)) (kc (nonce 4))) t (rb (nonce 2))
                     {{5
                     := bl (comm (V1 (nonce 0)) (kc (nonce 100))) t (rb (nonce 1))}} ({{6
                                                                          := bl (comm (V0 (nonce 0)) (kc (nonce 4))) t
                                                                               (rb (nonce 2))}}
                                                                          (t1)), (comm (V0 (nonce 0)) (kc (nonce 4)), kc (nonce 4)),
                  (ub (comm (V1 (nonce 0)) (kc (nonce 100))) t (rb (nonce 1))
                     {{5
                     := bl (comm (V1 (nonce 0)) (kc (nonce 100))) t (rb (nonce 1))}} ({{6
                                                                          := bl (comm (V0 (nonce 0)) (kc (nonce 4))) t
                                                                               (rb (nonce 2))}}
                                                                          (t0)),
                  (comm (V1 (nonce 0)) (kc (nonce 100)), kc (nonce 100))))
             else (|_, (comm (V0 (nonce 0)) (kc (nonce 4)), kc (nonce 4)), (|_, (comm (V1 (nonce 0)) (kc (nonce 100)), kc (nonce 100)))))]).
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

Axiom ext_blind_gen:  forall {n} (t t0 t1 : message) (z:mylist n), let v0 := (V0 (nonce 0)) in
                                                                                                      let v1 := (V1 (nonce 0)) in
                                                                                                      (|v0|#?|v1|) ## TRue ->  (Fresh (cons 1 (cons 2 (cons 3 (cons 4 nil)))) ([msg t, msg v0, msg v1, msg t0, msg t1])  = true) ->  closMylist ([msg t]) = true -> ((length (distMvars [msg t0, msg t1]))=?  2)%nat = true -> bVarMylist [msg t0, msg t1] = nil  ->
    let mvl:= (cons 5 (cons 6 nil)) in  (mVarMsg t0) = mvl /\ (mVarMsg t1) = mvl ->
                 let r0 := (r 1) in
                 let r1 := (r 2) in
                 let k0 := (kc (nonce 3)) in
                 let k1 := (kc (nonce 4)) in
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


