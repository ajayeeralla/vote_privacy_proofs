(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                     Rohit Chadha <chadhar@missouri.edu>              *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)
Load "core_axioms".

(** This library defines some tactics which will be used later and a theorem [IFTF].  #<br># *)

(** * Tactics *)

Ltac restr_proj p1  := apply RESTR_proj with (p:= p1) ; unfold proj_at_pos  ;  simpl.

Ltac restr_proj_in p1 H  := apply RESTR_proj with (p:= p1) in H ; unfold proj_at_pos in H ;  simpl in H.
Ltac dropone_in H:= restr_proj_in 1 H.
Ltac funapp_ses_in n1 n2 H := apply FUNCApp_session with (n:= n1)  (m:= n2) in H; simpl in H.

Ltac funapp_to_in  p1 H := apply FUNCApp_to with  (p:= p1) in H ; unfold to_at_pos in H; simpl in H.

Ltac funapp_EQ_M_in p3 p4 H := apply FUNCApp_EQ_M with  (p1:= p3 ) (p2:=p4) in H; unfold EQ_M_at_pos in H; simpl in H.

Ltac funapp_O_in  H := apply FUNCApp_O  in H; simpl in H.

Ltac funapp_act_in p1 H:= apply FUNCApp_act with (p:=p1) in H; unfold act_at_pos in H; simpl in H.

Ltac funapp_new_in H:= apply FUNCApp_new in H; simpl in H.

Ltac funapp_andB_in p3 p4 H := apply FUNCApp_andB with (p1:= p3) (p2:=p4) in H; unfold andB_at_pos in H; simpl in H.

Ltac funapp_acc_in  H1  := apply FUNCApp_acc  in H1;  simpl in H1.

Ltac funapp_elt_in n1 n2 :=
 match goal with 
| [H:  ?L1 ~ ?L2 |- _] => apply FUNCApp_elt with (p:=n1) (p1:= n2)  (ml1:= L1) (ml2:= L2) in H; unfold getelt_at_pos in H; simpl in H
 end .

Ltac funapp_exp_in  p4 p5 p6 H := apply FUNCApp_expatpos with  (p1:= p4) (p2:=p5) (p3:=p6) in H; unfold exp_at_pos in H; simpl in H .

Ltac restr_swap p3 p4 L1 L2 := 
   apply RESTR_swap with (p1:= p3) (p2 := p4) (ml1:= L1) (ml2:= L2) ; unfold swap_mylist ; simpl.

Ltac restr_swap_in p3 p4 H := apply RESTR_swap with (p1:= p3) (p2 := p4) in H; unfold swap_mylist in H;  simpl in H.

(** To apply a tactic [tac] for [n] times. *)

Ltac aply n tac :=
match n with 
| 0 =>  idtac
| S ?n' => tac ; aply n' tac
end.

(** To apply a tactic [tac] for [n] times in hypothesis [H]. *)

Ltac aply_in n tac H := 
match n with
| 0 =>  idtac
| S ?n' => tac H; aply_in n' tac H
end.
 
Ltac funapp_dropls H := apply RESTR_dropls  in H; unfold droplastsec in H; unfold proj_two in H; simpl in H.

Ltac Fr_pf := 
repeat match goal with 
| [ |- beq_nat ?X ?Y = ?Z] => destruct (beq_nat X Y) ;  match goal with | [H1: context [ if beq_nat ?X' ?Y' then ?Z' else ?Z''] |- _ ] =>  simpl in H1; repeat rewrite <- beq_nat_refl in H1 ; simpl in H1;  symmetry  end end; try assumption ; try reflexivity;
   repeat match goal with 
            | [ H : beq_nat ?X ?Y = _ |- _ ] =>  match goal with | [H1: context [ if beq_nat ?X ?Y then _ else _ ] |- _ ] =>  rewrite H in H1;  simpl in H1 end end; try assumption ; try reflexivity.

Ltac rew_all_hyps := simpl ; 
repeat match goal with 
| [H: beq_nat ?X ?Y = ?Z |- _] =>  match goal with | [ |- context [ if beq_nat ?X ?Y then _ else _ ] ] =>  rewrite H end;  repeat rewrite <- beq_nat_refl;  simpl; try reflexivity end.

Fixpoint beqnat  (n1:nat) (l: list nat) : list bool :=
match l with
| nil => nil
| cons h tl  => cons (beq_nat h n1) (beqnat n1 tl)
end.

Fixpoint beqnat_assns (l:list nat) : list bool :=
match l with
| nil => nil
| cons n1  tl => let x := (rev (removelast (rev l))) in

                   (app (beqnat n1 x) ( beqnat_assns tl))
end.

Ltac  beqnat_assns1 l :=
match l with
| nil => assert (true = true)
| cons ?h ?tl => assert h ; constr:tl
end.

Ltac length ls :=
  match ls with
    | [] => O
    |  _ :: ?ls' =>
      let ls'' := length ls' in
        constr:(S ls'')
  end.
 
Ltac Fr_prf := match goal with
                 |[|- Fresh ?X  ?Y = ?Z ] => length X
end.

(** Tactis that apply [IFBRANCH_M] repeateadly. *)

Ltac ifbr_t1  ml1 ml2 b b' x x' y y' := pose proof (IFBRANCH_M1 _ ml1 ml2 b b' x x' y y');
 match goal with
| [H : _ |-  (Cons _ _ (msg (if_then_else_M b x y)) ml1 ) ~  (Cons _ _ (msg (if_then_else_M b' x' y')) ml2 ) ] =>   apply H; clear H; try reflexivity
 end.

 Ltac ifbr1 :=
 match goal with
    | [ |-  (Cons _ _ (msg (if_then_else_M ?B ?X ?Y)) ?L1 )    ~  (Cons _ _ (msg (if_then_else_M ?B' ?X' ?Y')) ?L2 )  ] => ifbr_t1 L1 L2 B B' X X' Y Y'
 end.
 
Ltac ifbr_t2  ml1 ml2 b b' x1 x1' x2 x2' y1 y1' y2 y2' := pose proof (IFBRANCH_M2 _ ml1 ml2 b b' x1 x1' x2 x2' y1 y1' y2 y2');
 match goal with
| [H : _ |-  (Cons _ _ (msg (if_then_else_M b x1 y1)) (Cons _ _ (msg (if_then_else_M b x2 y2)) ml1 )) ~ (Cons _ _ (msg (if_then_else_M b' x1' y1')) (Cons _ _ (msg (if_then_else_M b' x2' y2')) ml2 )) ] =>   apply H; clear H; try reflexivity
                           end.
Ltac ifbr2 :=  match goal with
    | [ |-  (Cons _ _ (msg (if_then_else_M ?B ?X1 ?Y1)) (Cons _ _ (msg (if_then_else_M ?B ?X2 ?Y2)) ?L1 ))    ~  (Cons _ _ (msg (if_then_else_M ?B' ?X1' ?Y1')) (Cons _ _ (msg (if_then_else_M ?B' ?X2' ?Y2')) ?L2 ))  ] => ifbr_t2 L1 L2 B B' X1 X1' X2 X2' Y1 Y1' Y2 Y2'
               end.

Ltac ifbr_t3  ml1 ml2 b b' x1 x1' x2 x2' x3 x3' y1 y1' y2 y2' y3 y3' := pose proof (IFBRANCH_M2 _ ml1 ml2 b b' x1 x1' x2 x2' x3 x3' y1 y1' y2 y2' y3 y3');
 match goal with
| [H : _ |-  (Cons _ _ (msg (if_then_else_M b x1 y1)) (Cons _ _ (msg (if_then_else_M b x2 y2)) (Cons _ _ (msg (if_then_else_M b x3 y3)) ml1 ))) ~ (Cons _ _ (msg (if_then_else_M b' x1' y1')) (Cons _ _ (msg (if_then_else_M b' x2' y2')) (Cons _ _ (msg (if_then_else_M b' x3' y3')) ml2 ))) ] =>   apply H; clear H; try reflexivity
                           end.

Ltac ifbr3 :=  match goal with
    | [ |-  (Cons _ _ (msg (if_then_else_M ?B ?X1 ?Y1)) (Cons _ _ (msg (if_then_else_M ?B ?X2 ?Y2)) (Cons _ _ (msg (if_then_else_M ?B ?X3 ?Y3)) ?L1 )))    ~  (Cons _ _ (msg (if_then_else_M ?B' ?X1' ?Y1')) (Cons _ _ (msg (if_then_else_M ?B' ?X2' ?Y2')) (Cons _ _ (msg (if_then_else_M ?B' ?X3' ?Y3')) ?L2 )))  ] => ifbr_t3 L1 L2 B B' X1 X1' X2 X2' X3 X3' Y1 Y1' Y2 Y2' Y3 Y3'
               end.

Ltac ifbr_t4  ml1 ml2 b b' x1 x1' x2 x2' x3 x3' x4 x4' y1 y1' y2 y2' y3 y3' y4 y4' := pose proof (IFBRANCH_M2 _ ml1 ml2 b b' x1 x1' x2 x2' x3 x3' x4 x4' y1 y1' y2 y2' y3 y3' y4 y4');
 match goal with
| [H : _ |-  (Cons _ _ (msg (if_then_else_M b x1 y1)) (Cons _ _ (msg (if_then_else_M b x2 y2)) (Cons _ _ (msg (if_then_else_M b x3 y3)) (Cons _ _ (msg (if_then_else_M b x4 y4)) ml1 )))) ~ (Cons _ _ (msg (if_then_else_M b' x1' y1')) (Cons _ _ (msg (if_then_else_M b' x2' y2')) (Cons _ _ (msg (if_then_else_M b' x3' y3')) (Cons _ _ (msg (if_then_else_M b' x4' y4')) ml2 )))) ] =>   apply H; clear H; try reflexivity
 end.

Ltac ifbr4 :=  match goal with
    | [ |-  (Cons _ _ (msg (if_then_else_M ?B ?X1 ?Y1)) (Cons _ _ (msg (if_then_else_M ?B ?X2 ?Y2)) (Cons _ _ (msg (if_then_else_M ?B ?X3 ?Y3)) (Cons _ _ (msg (if_then_else_M ?B ?X4 ?Y4)) ?L1 ))))    ~  (Cons _ _ (msg (if_then_else_M ?B' ?X1' ?Y1')) (Cons _ _ (msg (if_then_else_M ?B' ?X2' ?Y2')) (Cons _ _ (msg (if_then_else_M ?B' ?X3' ?Y3')) (Cons _ _ (msg (if_then_else_M ?B' ?X4' ?Y4')) ?L2 ))))  ] => ifbr_t4 L1 L2 B B' X1 X1' X2 X2' X3 X3' X4 X4' Y1 Y1' Y2 Y2' Y3 Y3' Y4 Y4'
  end.

Ltac ifb := try ifbr4; try ifbr3; try ifbr2; try ifbr1.
(*
Ltac ifb := try ifbr1 ; try simpl; try reflexivity; try unf_qb; try unf_qd.
*)

Ltac simpl_Hyps :=
repeat match goal with 
  | [H: _ |- _ ] => simpl in H
    end.

Definition len_mylist {n} (l:mylist n) := n.
Ltac funapp_os p1 t1  := match goal with 
| [H:  ?L1 ~ ?L2 |- _] => apply FUNCApp_os with (p:= p1) (n:= len_mylist L1) (t:= t1) (ml1:= L1) (ml2:= L2) in H; simpl in H
end .

Ltac funos p H1 :=
repeat match goal with  
    | [ |-  (Cons _ _ (msg ?B1 ) _ ) ~ (Cons _ _ (msg ?B2) _) ] => funapp_os p (msg B1) H1
  end.
Ltac DDH2 := assert(DDH1: Fresh [0;1;2;4] [] = true);try reflexivity; try apply DDH in DDH1.

Axiom RESTR_rev: forall {m} (ml1 ml2: mylist m), ml1 ~ ml2 -> (reverse ml1) ~ (reverse ml2).

(** To apply [FRESHIND] *)

Ltac fr_ind n1 n2 H1 := 
match goal with
|[ H1: ?L1 ~ ?L2 |- _ ] => assert(  ((clos_mylist (L1++L2)) = true) /\ ( (Fresh [ n1] (L1++L2)) = true) /\ ( (Fresh [ n2] ( L1 ++ L2)) = true) /\  (L1 ~ L2))
end.

Ltac aply_fr_ind :=
match goal with
| [ H5: context[clos_mylist _ ] |- _] => apply FRESHIND in H5; simpl in H5
end.
Ltac fresh_ind n1 n2 H := fr_ind n1 n2 H; repeat ( try split;  simpl;  try reflexivity ; try assumption); aply_fr_ind.

(** To apply FUNCApp *)
  
Ltac funapp_fm_in  g H :=  apply FUNCApp_mconst with (m:= g) in H ; simpl in H.
Ltac funapp_f1_in g n1 H := apply FUNCApp_f1 with (f1:= g) (p:= n1) in H ; simpl in H.
Ltac funapp_f2b_in g n1 n2 H:= apply FUNCApp_f2b with (f2b:= g) (p1:= n1) (p2:= n2) in H ; simpl in H.
Ltac funapp_f2m_in g n1 n2 H:= apply FUNCApp_f2m with (f2m:= g) (p1:= n1) (p2:= n2) in H ; simpl in H.
Ltac funapp_f3b_in g n1 n2 n3 H:= apply FUNCApp_f3b with (f3b:= g) (p1:= n1) (p2:= n2) (p3:= n3) in H; simpl in H.
Ltac funapp_f3bm_in g n1 n2 n3 H:= apply FUNCApp_f3bm with (f3bm:= g) (p1:= n1) (p2:= n2) (p3:= n3) in H; simpl in H.
Ltac funapp_f3m_in g n1 n2 n3 H:= apply FUNCApp_f3m with (f3m:= g) (p1:= n1) (p2:= n2) (p3:=n3) in H; simpl in H.
Ltac funapp_f4m_in g n1 n2 n3 n4 H:= apply FUNCApp_f4m with (f4m:= g) (p1:= n1) (p2:= n2) (p3:= n3) (p4:= n4)  in H; simpl in H.
Ltac funapp_sublist_in n1 n2 H:= apply FUNCApp_sublist with (m:= n1) (n:= n2) in H; unfold sublist in H; simpl in H.

(** To apply RESTR *)

Ltac reswap_in n1 n2 H:= apply RESTR_swap with (p1:= n1) (p2:= n2) in H; unfold swap_mylist in H; simpl in H.
Ltac reproj_in n1 n2 H:= apply RESTR_proj with (p1:= n1) (p2:= n2) in H; unfold proj_at_pos in H; simpl in H.
Ltac restrproj_in n1 H  := apply  RESTR_proj with (p:= n1) in H; unfold proj_at_pos  in H; simpl in H.
Ltac funapp_notB_in n H :=
apply FUNCApp_notB with (p:= n) in H; unfold notB_at_pos in H; simpl in H.

(** * [IFTF] *)
(** The theorem states that for any [b], [ if b then true else false = b ]. Notice that we use [#] (resp. [##]) for [message] (resp. [Bool]) in lieu of [=]. *)

Theorem IFTF:  forall (n:nat),  (if_then_else_B (Bvar n) TRue FAlse) ## (Bvar n).
Proof.
intros.
rewrite <- (IFSAME_B (Bvar n) (Bvar n)) at 2.
rewrite -> IFEVAL_B with (b1 := (Bvar n)).
simpl.
rewrite <- beq_nat_refl.
reflexivity.
Qed.

Theorem IFTFb : forall (b:Bool),  (if_then_else_B b TRue FAlse) ## b.
Proof. intros;pose proof(IFTF 0); apply Forall_ELM_EVAL_B with (n:=0) (b:=b) in H; simpl in H; auto. Qed.
