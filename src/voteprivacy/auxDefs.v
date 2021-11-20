(************************************************************************)
(* Copyright (c) 2017-2018, Ajay Kumar Eeralla <ae266@mail.missouri.edu>*)
(************************************************************************)

Require Export destructTerm.
Require Import Coq.Bool.Bool.
Set Nested Proofs Allowed.
Require Import List.
Import ListNotations.

Section auxProps.
  Axiom ifMorphPair2: forall b t1 t2 t3, (t1, If b then t2 else t3) # If b then (t1, t2) else (t1, t3).
  Axiom ifMorphPair1: forall b t1 t2 t3, (If b then t1 else t2, t3) # If b then (t1, t3) else (t2, t3).
  Axiom ifMorphf3: forall b t1 t2 t3 t4 {f: message-> message -> message -> Bool}, (f t1 t2 (If b then t3 else t4)) ## (IF b then (f t1 t2 t3) else (f t1 t2 t4)).
  Axiom ifMorphf3b_fst: forall b t1 t2 t3 t4 {f: message-> message -> message -> message}, (f (If b then t1 else t2) t3 t4) # (If b then (f t1 t3 t4) else (f t2 t3 t4)).
  Axiom andB_elim: forall b1 b2 t1 t2, (If b1 & b2 then t1 else t2) # (If b1 then (If b2 then t1 else t2) else t2).
  Axiom ifMorphIfThen: forall b1 b2 t1 t2 t3, (If b1 then (If b2 then t1 else t2) else t3) # (If b2 then (If b1 then t1 else t3) else (If b1 then t2 else t3)).
  Axiom orB_FAlse_r: forall b, b or FAlse = b.
  Axiom orB_FAlse_l: forall b, FAlse or b = b.
  Axiom ifMorphIf: forall b1 b2 b3 b4 t1 t2, (If b1 & (IF b2 then b3 else b4) then t1 else t2) # (If b2 then (If b1 & b3 then t1 else t2) else (If b1 & b4 then t1 else t2)).
  Fixpoint ifMorphDef (f: Mlist -> message) (al: Mlist) (l: Mlist) :=
    match l with
    | nil => f (al ++ nil)
    | cons (If b then t1 else t2) nil  => If b then (f (al ++ (cons t1 nil))) else (f (al ++ (cons t2 nil)))
| h :: tl => match h with
             | If b then t1 else t2 => If b then (ifMorphDef f (al ++ (cons t1 nil)) tl) else (ifMorphDef f (al ++ (cons t2 nil)) tl)
| _ => ifMorphDef f (al ++ (cons h nil)) tl
  end
  end.
  Axiom clos_sub_vtrm: forall n1 s1 n2 s2 t, let mvl:= (distMvars [msg t]) in (cons n1  (cons n2 nil))= mvl \/ (cons n2 (cons n1 nil)) = mvl -> closMsg ({{n1:=s1}} ({{n2:=s2}}t)) = true.

  (* Compute ifMorphDef f nil [O; If FAlse then nonce 1 else O; nonce 2; If TRue then (If TRue then nonce 100 else O) else nonce 4]. *)
  Axiom ifMorphAttComp: forall l, (f l) # (ifMorphDef f nil l).
  End auxProps.

  (* Axiom ifMorphAttComp: forall b f l t, (If b then (f l) else t) # (If b then (ifMorphDef f nil l) else t). *)
 Open Scope msg_scope.
(* Section auxTacs. *)
  Ltac rew_ifMorphIf :=
    match goal with
    |[|- context[(If ?B1 & (IF ?B2 then ?B3 else ?B4) then ?T1 else ?T2)] ] => rewrite (@ifMorphIf B1 B2 B3 B4 T1 T2)
    end.
  Ltac apply_ifbr ml1 ml2 b b' x x' y y' := apply (@IFBRANCH_M1 _ ml1 ml2 b b' x x' y y'); simpl.
  Ltac aply_ifbr :=
    match goal with
    | [|- [msg (If ?B1 then ?T1 else ?F1)]
            ~ [msg (If ?B2 then ?T2 else ?F2)] ]
      => apply_ifbr [] [] B1 B2 T1 T2 F1 F2
    | [|- [?X1, msg (If ?B1 then ?T1 else ?F1)]
            ~ [?Y1, msg (If ?B2 then ?T2 else ?F2)] ]
      => apply_ifbr [X1] [Y1] B1 B2 T1 T2 F1 F2
    | [|- [?X1, ?X2, msg (If ?B1 then ?T1 else ?F1)]
            ~ [?Y1, ?Y2, msg (If ?B2 then ?T2 else ?F2)] ]
      => apply_ifbr [X1, X2] [Y1, Y2] B1 B2 T1 T2 F1 F2
    | [|- [?X1, ?X2, ?X3, msg (If ?B1 then ?T1 else ?F1)]
            ~ [?Y1, ?Y2, ?Y3, msg (If ?B2 then ?T2 else ?F2)] ]
      => apply_ifbr [X1, X2, X3] [Y1, Y2, Y3] B1 B2 T1 T2 F1 F2
    | [|- [?X1, ?X2, ?X3, ?X4, msg (If ?B1 then ?T1 else ?F1)]
            ~ [?Y1, ?Y2, ?Y3, ?Y4, msg (If ?B2 then ?T2 else ?F2)] ]
      => apply_ifbr [X1, X2, X3, X4] [Y1, Y2, Y3, Y4] B1 B2 T1 T2 F1 F2
    | [|- [?X1, ?X2, ?X3, ?X4, ?X5, msg (If ?B1 then ?T1 else ?F1)]
            ~ [?Y1, ?Y2, ?Y3, ?Y4, ?Y5, msg (If ?B2 then ?T2 else ?F2)] ]
      => apply_ifbr [X1, X2, X3, X4, X5] [Y1, Y2, Y3, Y4, Y5] B1 B2 T1 T2 F1 F2
    | [|- [?X1, ?X2, ?X3, ?X4, ?X5, ?X6, msg (If ?B1 then ?T1 else ?F1)]
            ~ [?Y1, ?Y2, ?Y3, ?Y4, ?Y5, ?Y6, msg (If ?B2 then ?T2 else ?F2)] ]
      => apply_ifbr [X1, X2, X3, X4, X5, X6] [Y1, Y2, Y3, Y4, Y5, Y6] B1 B2 T1 T2 F1 F2
    | [|- [?X1, ?X2, ?X3, ?X4, ?X5, ?X6, ?X7, msg (If ?B1 then ?T1 else ?F1)]
            ~ [?Y1, ?Y2, ?Y3, ?Y4, ?Y5, ?Y6, ?Y7, msg (If ?B2 then ?T2 else ?F2)] ]
      => apply_ifbr [X1, X2, X3, X4, X5, X6, X7] [Y1, Y2, Y3, Y4, Y5, Y6, Y7] B1 B2 T1 T2 F1 F2
                    (** extend this for other cases *)
    end.

  Proposition freshNeqExt: forall (n: nat) (m: message), ^? m = true /\ (Fresh (cons n nil) [msg m]) = true -> ((nonce n) #? m) ## FAlse.
Proof. intros. pose proof(FRESHNEQ n m).
       apply (@Example10_B ((nonce n)#?m) FAlse FAlse).
       unfold const; auto.
Qed.
Ltac aply_freshneq n :=
  match goal with
  |[|-context[ (nonce n) #? ?X] ] =>  pose proof(@freshNeqExt n X) as tmp; rewrite tmp; try unfold Fresh; try auto
  end.
Axiom compHid: forall (n1 n2: nat) (t1 t2: message) {n} (z: mylist n),
    closMylist [msg t1, msg t2] = true /\ closMylist z = true /\
      Fresh [n1; n2] ([msg t1, msg t2]++z)%msg = true ->
    (|t1|#?|t2|) ## TRue ->
    (z ++ [msg (comm t1 (k n1)), msg (comm t2 (k n2))]) ~ (z ++ [msg (comm t2 (k n1)), msg (comm t1 (k n2))]).

Proposition vchecksImplyVoteEql: (vcheck (v 0)) & (vcheck (v 1)) ## TRue -> (|v 0| #? |v 1|) ## TRue.
Proof. intros.
       pose proof(vote_len_eql).
       rewrite H in H0; unfold v in H0; red_in H0; try auto.
Qed.
Ltac aplyCompHid :=
  match goal with
  | [|- [msg (comm ?V0 (kc (nonce ?N2))), msg (comm ?V1 (kc (nonce ?N3)))]
          ~ [msg (comm _ (kc (nonce _))), msg (comm _ (kc (nonce _)))] ]
    => apply (@compHid N2 N3 V0 V1 _ []%msg); try apply vchecksImplyVoteEql; try auto; try assumption
  end.

(* End auxTacs. *)
(* Definition V (b:bool) := *)
(*     match b with *)
(*     | false => (V0 (nonce 0)) *)
(*     | true => (V1 (nonce 0)) *)
(*     end. *)

(*   Definition cn (b:bool) :nat := *)
(*     match b with *)
(*     | false => 0 *)
(*     | true => 1 *)
(*     end. *)
(* SearchAbout eqb%bool. *)
(** abbreviations *)

Definition sr n := rs (nonce n).
Definition t0 seed1 seed2 := (((vk 0), (Mvar 0), sign (Mvar 0) (ssk 0) (sr seed1)), ((vk 1), (Mvar 1), sign (Mvar 1) (ssk 1) (sr seed2))).

Definition tau n (m:message) := match n, m with
                                | 1, m => (pi1 m)
                                | 2, m => (pi1 (pi2 m))
                                | 3, m => (pi2 (pi2 m))
                                | _, _ => O
                                end.

Definition d n x := (dec (tau n x) (ske 11)).
Definition pvchecks x := ((pi2 (d 1 x)) #? TWO) & ((pi2 (d 2 x)) #? TWO) & ((pi2 (d 3 x)) #? TWO).
Definition pochecks x := ((tau 3 (d 1 x)) #? THREE) & ((tau 3 (d 2 x)) #? THREE) & ((tau 3 (d 3 x)) #? THREE).

Definition dist x := !((d 1 x) #? (d 2 x)) & !((d 1 x) #? (d 3 x))& ! ((d 2 x) #? (d 3 x)).
Definition isin (x y:message):Bool := (x #? (tau 1 y)) or (x #? (tau 2 y)) or (x #? (tau 3 y)).
Definition bcheck (x y:message):Bool := (isin x ((tau 1 (pi2 (tau 1 y))), ((tau 1 (pi2 (tau 2 y))), (tau 1 (pi2 (tau 3 y)))))).
Definition ncheck (x y:message):Bool := (isin x ((tau 3 (pi2 (tau 1 y))), ((tau 3 (pi2 (tau 2 y))), (tau 3 (pi2 (tau 3 y)))))).


                            Definition lbl:= |(nonce 100)|.
Definition label x y := If (x #? (tau 2 (pi2 (tau 1 y)))) then (pi1 (tau 1 y))
                           else  (If (x#? (tau 2 (pi2 (tau 2 y)))) then (pi1 (tau 2 y))
                                                       else (If (x #? (tau 2 (pi2 (tau 3 y)))) then (pi1 (tau 3 y))
                                                             else O)).

Definition bnlcheck( x y z:message):Bool:= (bcheck x z) & (|(label x z)| #? lbl) & (ncheck y z).

Definition mvchecks x (n n':nat) := (dist (x n n')) & (pvchecks (x n n')).

Definition p n x := ( (tau 1 (d n x)), (tau 2 (d n x))).

Definition sotrm x := (shufl (p 1 x) (p 2 x) (p 3 x)).

Definition isink (x y:message):Bool := (x #? (tau 2 (d 1 y))) or (x #? (tau 2 (d 2 y))) or (x #? (tau 2 (d 3 y))).

Lemma tau1: forall x y z, (tau 1 (x, (y, z))) # x.
Proof. intros. unfold tau. rewrite proj1; auto. reflexivity.
Qed.
Lemma tau2: forall x y z, (tau 2 (x, (y, z))) # y.
Proof. intros. unfold tau; rewrite proj2, proj1;auto. reflexivity. Qed.
Lemma tau3: forall x y z, (tau 3 (x, (y, z))) # z.
Proof. intros. unfold tau. repeat rewrite proj2; try reflexivity.
Qed.
(* better to apply nodup seperately *)
Axiom nodup: forall {m} (l1 l2: mylist m), let l1' := conv_mylist_listos l1 in
                                           let l2' := conv_mylist_listos l2 in
                                           let l1'' := noDup l1' in
                                           let l2'' := noDup l2' in
                                           let y:= oslToMylist l1'' l2'' in
                                           (pi1ProdMylist y) ~ (pi2ProdMylist y) -> l1 ~ l2.

Axiom cca2Trans: forall {m} {l1 l2 l1' l2': mylist m}, l1 ~ l1' /\ l2 ~ l2' /\ l1' ~ l2' -> l1 ~ l2.
Ltac aply_cca2Trans L R :=
  match goal with
  | [|- ?X ~ ?Y] => apply (@cca2Trans _ X Y L R); try split
  end.

Ltac aplyCCA2 n n1 n2 n3 u u' := aplyDestrEnc 11 7; apply nodup; simpl;
  match goal with
  | [|- ?X ~ ?Y] => apply (@subMvarEnc n n1 n2 n3 u u' _ X Y); simpl; (* replace encryptions with (Mvar n) *)
                    match goal with
                    | [|- ?X1 ~ ?Y1] => apply (@rewDecs n n1 u u' _ X1 Y1); simpl; (* rewrite decryptions to pass the cca2compliance *)
                                        match goal with
                                        |[|- ?X2 ~ ?Y2] => apply (@ENCCCA2 n n1 n2 n3 u u' _ X2); repeat (try apply len_reg; try rewrite eqmeql; try apply nameEql; try simpl; try intuition)
                                        end
                    end
  end.
(* Some stuff *)
Axiom funcapp_f1m': forall {n n'} f p1 (z z':mylist n) (z1 z1':mylist n'), (z ++ z1) ~ (z' ++ z1') -> ((z ++ z1) ++ [msg (f (ostomsg (getelt_at_pos p1 z1)))]) ~ ((z' ++ z1') ++ [msg (f (ostomsg (getelt_at_pos p1 z1')))]).
Ltac funcapp_f1m'_in g n H:= apply funcapp_f1m' with (f:=g) (p1:=n) in H; unfold getelt_at_pos in H; simpl in H.
Axiom ifmor_ifm: forall f b x y, (f (If b then x else y)) # (If b then (f x) else (f y)).

Lemma extFuncapp1: forall n b b' x x' y y' (z z': mylist n) g, (z ++ [bol b, msg (If b then x else y)]) ~ (z' ++ [bol b', msg (If b' then x' else y')]) -> (z ++ [bol b, msg (If b then x else y), msg (If b then (g x) else |_)])~ (z' ++ [bol b', msg (If b' then x' else y'), msg (If b' then (g x') else |_)]).
Proof. intros.
       funcapp_f1m'_in g 2 H.
       simpl.
       repeat rewrite ifmor_ifm in H.
       funcapp_fm_last |_ H; auto. apply ind_assoc in H; simpl in H.
       apply funcapp_f3bm' with (f:= (ifm_then_else_)) (p1:= 1) (p2:=3) (p3:=4) in H; unfold getelt_at_pos; simpl in H.
       simpl in H.
       (********************)
       apply ind_assoc in H; simpl in H.
       do 2  apply restr with (p:= droplastsec) in H; unfold droplastsec in H; simpl in H; simpl; try rewrite Nat.eqb_refl; auto.
       repeat rewrite aply_ifeval_gen in H;auto. Qed.
