(************************************************************************)
(* Copyright (c) 2017-2018, Ajay Kumar Eeralla <ae266@mail.missouri.edu>*)     
(************************************************************************)
Require Export eqNonce.

(** This library defines some tactics which will be used later and a theorem [IFTF].  #<br># *)

(** * Tactics *)

Ltac restr_proj p1  := apply RESTR_proj with (p:= p1) ; unfold proj_at_pos  ;  simpl.

Ltac restr_proj_in p1 H  := apply RESTR_proj with (p:= p1) in H ; unfold proj_at_pos in H ;  simpl in H.
Ltac dropone_in H:= restr_proj_in 1 H.
 
Ltac dropLast_in H1 :=
  match goal with
  | [H: ?L1~?L2 |- _] => match H with
                           | H1 =>  restr_proj_in (length (toListm L1)) H
                         end
                           end.
(*
Ltac funapp_ses_in n1 n2 H := apply FUNCApp_session with (n:= n1)  (m:= n2) in H; simpl in H.
*)
Ltac funapp_to_in  p1 H := apply FUNCApp_to with  (p:= p1) in H ; unfold to_at_pos in H; simpl in H.

Ltac funapp_eqm_in p3 p4 H := apply FUNCApp_eqm with  (p1:= p3 ) (p2:=p4) in H; unfold eqm_at_pos in H; simpl in H.

Ltac funapp_O_in  H := apply FUNCApp_O  in H; simpl in H.
(*
Ltac funapp_act_in p1 H:= apply FUNCApp_act with (p:=p1) in H; unfold act_at_pos in H; simpl in H.
Ltac funapp_new_in H:= apply FUNCApp_new in H; simpl in H.
*)
Ltac funapp_andB_in p3 p4 H := apply FUNCApp_andB with (p1:= p3) (p2:=p4) in H; unfold andB_at_pos in H; simpl in H.
(*
Ltac funapp_acc_in  H1  := apply FUNCApp_acc  in H1;  simpl in H1.
 *)
(*
Ltac funapp_elt_in n1 n2 :=
 match goal with 
| [H:  ?L1 ~ ?L2 |- _] => apply FUNCApp_elt with (p:=n1) (p1:= n2)  (ml1:= L1) (ml2:= L2) in H; unfold getelt_at_pos in H; simpl in H
 end .

Ltac funapp_exp_in  p4 p5 p6 H := apply FUNCApp_expatpos with  (p1:= p4) (p2:=p5) (p3:=p6) in H; unfold exp_at_pos in H; simpl in H .
*)
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
| cons ?h ?tl => assert h ; tl
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
| [H : _ |-  (Cons _ _ (msg (ifm_then_else_ b x y)) ml1 ) ~  (Cons _ _ (msg (ifm_then_else_ b' x' y')) ml2 ) ] =>   apply H; clear H; try reflexivity
 end.

 Ltac ifbr1 :=
 match goal with
    | [ |-  (Cons _ _ (msg (ifm_then_else_ ?B ?X ?Y)) ?L1 )    ~  (Cons _ _ (msg (ifm_then_else_ ?B' ?X' ?Y')) ?L2 )  ] => ifbr_t1 L1 L2 B B' X X' Y Y'
 end.
 
Ltac ifbr_t2  ml1 ml2 b b' x1 x1' x2 x2' y1 y1' y2 y2' := pose proof (IFBRANCH_M2 _ ml1 ml2 b b' x1 x1' x2 x2' y1 y1' y2 y2');
 match goal with
| [H : _ |-  (Cons _ _ (msg (ifm_then_else_ b x1 y1)) (Cons _ _ (msg (ifm_then_else_ b x2 y2)) ml1 )) ~ (Cons _ _ (msg (ifm_then_else_ b' x1' y1')) (Cons _ _ (msg (ifm_then_else_ b' x2' y2')) ml2 )) ] =>   apply H; clear H; try reflexivity
                           end.
Ltac ifbr2 :=  match goal with
    | [ |-  (Cons _ _ (msg (ifm_then_else_ ?B ?X1 ?Y1)) (Cons _ _ (msg (ifm_then_else_ ?B ?X2 ?Y2)) ?L1 ))    ~  (Cons _ _ (msg (ifm_then_else_ ?B' ?X1' ?Y1')) (Cons _ _ (msg (ifm_then_else_ ?B' ?X2' ?Y2')) ?L2 ))  ] => ifbr_t2 L1 L2 B B' X1 X1' X2 X2' Y1 Y1' Y2 Y2'
               end.

Ltac ifbr_t3  ml1 ml2 b b' x1 x1' x2 x2' x3 x3' y1 y1' y2 y2' y3 y3' := pose proof (IFBRANCH_M2 _ ml1 ml2 b b' x1 x1' x2 x2' x3 x3' y1 y1' y2 y2' y3 y3');
 match goal with
| [H : _ |-  (Cons _ _ (msg (ifm_then_else_ b x1 y1)) (Cons _ _ (msg (ifm_then_else_ b x2 y2)) (Cons _ _ (msg (ifm_then_else_ b x3 y3)) ml1 ))) ~ (Cons _ _ (msg (ifm_then_else_ b' x1' y1')) (Cons _ _ (msg (ifm_then_else_ b' x2' y2')) (Cons _ _ (msg (ifm_then_else_ b' x3' y3')) ml2 ))) ] =>   apply H; clear H; try reflexivity
                           end.

Ltac ifbr3 :=  match goal with
    | [ |-  (Cons _ _ (msg (ifm_then_else_ ?B ?X1 ?Y1)) (Cons _ _ (msg (ifm_then_else_ ?B ?X2 ?Y2)) (Cons _ _ (msg (ifm_then_else_ ?B ?X3 ?Y3)) ?L1 )))    ~  (Cons _ _ (msg (ifm_then_else_ ?B' ?X1' ?Y1')) (Cons _ _ (msg (ifm_then_else_ ?B' ?X2' ?Y2')) (Cons _ _ (msg (ifm_then_else_ ?B' ?X3' ?Y3')) ?L2 )))  ] => ifbr_t3 L1 L2 B B' X1 X1' X2 X2' X3 X3' Y1 Y1' Y2 Y2' Y3 Y3'
               end.

Ltac ifbr_t4  ml1 ml2 b b' x1 x1' x2 x2' x3 x3' x4 x4' y1 y1' y2 y2' y3 y3' y4 y4' := pose proof (IFBRANCH_M2 _ ml1 ml2 b b' x1 x1' x2 x2' x3 x3' x4 x4' y1 y1' y2 y2' y3 y3' y4 y4');
 match goal with
| [H : _ |-  (Cons _ _ (msg (ifm_then_else_ b x1 y1)) (Cons _ _ (msg (ifm_then_else_ b x2 y2)) (Cons _ _ (msg (ifm_then_else_ b x3 y3)) (Cons _ _ (msg (ifm_then_else_ b x4 y4)) ml1 )))) ~ (Cons _ _ (msg (ifm_then_else_ b' x1' y1')) (Cons _ _ (msg (ifm_then_else_ b' x2' y2')) (Cons _ _ (msg (ifm_then_else_ b' x3' y3')) (Cons _ _ (msg (ifm_then_else_ b' x4' y4')) ml2 )))) ] =>   apply H; clear H; try reflexivity
 end.

Ltac ifbr4 :=  match goal with
    | [ |-  (Cons _ _ (msg (ifm_then_else_ ?B ?X1 ?Y1)) (Cons _ _ (msg (ifm_then_else_ ?B ?X2 ?Y2)) (Cons _ _ (msg (ifm_then_else_ ?B ?X3 ?Y3)) (Cons _ _ (msg (ifm_then_else_ ?B ?X4 ?Y4)) ?L1 ))))    ~  (Cons _ _ (msg (ifm_then_else_ ?B' ?X1' ?Y1')) (Cons _ _ (msg (ifm_then_else_ ?B' ?X2' ?Y2')) (Cons _ _ (msg (ifm_then_else_ ?B' ?X3' ?Y3')) (Cons _ _ (msg (ifm_then_else_ ?B' ?X4' ?Y4')) ?L2 ))))  ] => ifbr_t4 L1 L2 B B' X1 X1' X2 X2' X3 X3' X4 X4' Y1 Y1' Y2 Y2' Y3 Y3' Y4 Y4'
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
(*Ltac funapp_os p1 t1  := match goal with 
| [H:  ?L1 ~ ?L2 |- _] => apply FUNCApp_os with (p:= p1) (n:= len_mylist L1) (t:= t1) (ml1:= L1) (ml2:= L2) in H; simpl in H
end .

Ltac funos p H1 :=
repeat match goal with  
    | [ |-  (Cons _ _ (msg ?B1 ) _ ) ~ (Cons _ _ (msg ?B2) _) ] => funapp_os p (msg B1) H1
  end. *)
(*
Ltac DDH2 := assert(DDH1: Fresh [0;1;2;4] [] = true);try reflexivity; try apply DDH in DDH1.
*)
Axiom RESTR_rev: forall {m} (ml1 ml2: mylist m), ml1 ~ ml2 -> (reverse ml1) ~ (reverse ml2).

(** To apply [FRESHIND] *)

Ltac fr_ind n1 n2 H1 := 
match goal with
|[ H1: ?L1 ~ ?L2 |- _ ] => assert(  ((closMylist (L1++L2)) = true) /\ ( (Fresh [ n1] (L1++L2)) = true) /\ ( (Fresh [ n2] ( L1 ++ L2)) = true) /\  (L1 ~ L2))
end.

Ltac aply_fr_ind :=
match goal with
| [ H5: context[closMylist _ ] |- _] => apply FRESHIND in H5; simpl in H5
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

(** Some tactics defined here *)

Ltac redg := try rewrite IFTRUE_M ; try rewrite IFFALSE_M ; try rewrite IFSAME_M ;try rewrite IFTRUE_B ; try rewrite IFFALSE_B ; try rewrite IFSAME_B. (* try rewrite IFTFb.*)

Ltac red_in H:= try rewrite IFTRUE_M in H; try rewrite IFFALSE_M in H; try rewrite IFSAME_M in H;try rewrite IFTRUE_B in H; try rewrite IFFALSE_B in H; try rewrite IFSAME_B in H. (* try rewrite IFTFb in H.*)

(************rewrite hypothesis************)

Ltac rew_clear H := rewrite H ; simpl; clear H.
Ltac rew_clear_in H H1:= rewrite H in H1; simpl in  H1 ;clear H .

(*****************************Forall elimination ***************************)

Ltac fall_elm_in n1 b1 H := try apply Forall_ELM_EVAL_B with (n:= n1) (b:= b1) in H;  try apply Forall_ELM_EVAL_M with (n:= n1) (x:= b1) in H; simpl in H; try rewrite H.

Ltac fall_elm n1 b1  :=  try apply Forall_ELM_EVAL_B with (n:= n1) (b:= b1) ;  try apply Forall_ELM_EVAL_M with (n:= n1) (x:= b1) ;  simpl.

(*******************& elimination *******************)
(*Ltac andB_elm_msg n1 t1 t2  := pose proof( mor_eval_andB n1 t1 t2) ;
match goal with
| [H : ?X # ?Y |- _ ] =>    simpl in H ; match goal with | [H : ?X # ?Y |- _ ] =>   rewrite H; clear H end
         
 end.

Ltac andB_elm_msg_in n1 t1 t2 H1 := pose proof( mor_eval_andB n1 t1 t2) ;
match goal with
| [H : ?X # ?Y |- _ ] =>    simpl in H ; rewrite H in H1; clear H 
         
 end.

Ltac rew_andB_elm_msg :=
repeat match goal with 
|[H: _ |-  context [(ifm_then_else_  ((Bvar ?n2) & ?P) ?X ?Y )] ] => andB_elm_msg n2 X Y 
end.

Ltac rew_andB_elm_in_msg H1 := 
repeat match goal with
 |[H: context [(ifm_then_else_ ((Bvar ?n2) & ?P) ?X ?Y )] |- _ ] =>  andB_elm_msg_in n2 X Y H1 end.

(***********************not sure if we require them*****)

Ltac andB_elm_bol n1 t1 t2  := pose proof( mor_eval_andB n1 t1 t2) ;
match goal with
| [H : ?X # ?Y |- _ ] =>    simpl in H ;  match goal with | [H : ?X # ?Y |- _ ] =>   rewrite H; clear H end
      end.

Ltac  andB_elm_bol_in n1 t1 t2 H1  := pose proof( mor_eval_andB n1 t1 t2) ;
match goal with
| [H : ?X # ?Y |- _ ] =>    simpl in H ;    rewrite H in H1; clear H 
        
 end.

Ltac rew_andB_elm_bol :=
repeat match goal with 
|[H: _ |-  context [(ifb ((Bvar ?n2) & ?P) ?X ?Y )] ] => andB_elm_bol  n2 X Y 
end.

Ltac rew_andB_elm_in_bol H1 := 
repeat match goal with
 |[H: context [(ifb ((Bvar ?n2) & ?P) ?X ?Y )] |- _ ] =>  andB_elm_bol_in n2 X Y H1 end.

(******************************************IFTF***********************************)

Ltac rew_IFTF b  := pose proof(IFTFb b); 
match goal with
| [H : _ |- ?X ## ?Y ] =>  rewrite H ; clear H; simpl
end.

Ltac rew_IFTF_in b H1  := pose proof(IFTFb b);
match goal with
  | [H : ?X ## ?Y |- _ ] =>   rewrite H in H1 ; clear H; simpl in H1
end.

Ltac rew_IFTF_all_in H1  := 
repeat match goal with 
|[ H : context [  (ifb ?X TRue FAlse)]   |- _ ] => rew_IFTF_in X H1 
end. 

Ltac rew_IFTF_all  := 
repeat match goal with 
|[ H : _ |-  context [ ifb ?X TRue FAlse ]  ] => rew_IFTF X 
end. 

(*************IFM_THEN_ELSE_ORPH*****message_bool*******)

Ltac ifm_then_else_or_msg_bol n1 b1 b2 t1 t2  := pose proof(IFM_THEN_ELSE_ORPH_M2 n1 b1 b2 t1 t2);
match goal with
| [H : _ |-  ?X # ?Y ] =>    simpl in H ; match goal with | [H : ?X # ?Y |- _ ] =>   rewrite H; clear H end
       end.

Ltac ifm_then_else_or_msg_bol_in n1 b1 b2 t1 t2 H1 := pose proof(IFM_THEN_ELSE_ORPH_M2 n1 b1 b2 t1 t2);
match goal with
| [H : ?X # ?Y |- _ ] =>    simpl in H ; match goal with | [H : ?X # ?Y |- _ ] =>   rewrite H in H1; clear H end
       end.

Ltac rew_ifm_then_else_or_msg_bol :=
repeat match goal with 
|[ H : _ |-  context [ ifm_then_else_ (ifb (Bvar ?n1) ?Y ?Z) ?P ?Q]  ] => ifm_then_else_or_msg_bol n1 Y Z P Q
end. 

Ltac rew_ifm_then_else_or_msg_bol_in H1 :=
repeat match goal with 
|[ H : context [ ifm_then_else_ (ifb (Bvar ?n1) ?Y ?Z) ?P ?Q]   |- _ ] => ifm_then_else_or_msg_bol_in n1 Y Z P Q H1
end. 

(********************IFM_THEN_ELSE_RPH***********Bool_Bool_fst*****************)

Ltac ifm_then_else_or_bol_bol_fst n1 b1 b2 b3 b4  := pose proof(IFM_THEN_ELSE_ORPH_B2 n1 b1 b2 b3 b4);
match goal with
| [H :_ |-  ?X ## ?Y ] =>    simpl in H ; match goal with | [H : ?X ## ?Y |- _ ] =>   rewrite H; clear H end
         end.

Ltac ifm_then_else_or_bol_bol_fst_in  n1 b1 b2 b3 b4 H1 := pose proof(IFM_THEN_ELSE_ORPH_B2 n1 b1 b2 b3 b4);
match goal with
| [H : ?X ## ?Y |- _ ] =>    simpl in H ; match goal with | [H : ?X ## ?Y |- _ ] =>   rewrite H in H1; clear H end
  end.

Ltac rew_ifm_then_else_or_bol_bol_fst :=
repeat match goal with 
|[ H : _ |-  context [ ifb (ifb (Bvar ?n1) ?Y ?Z) ?P ?Q]  ] =>  ifm_then_else_or_bol_bol_fst n1 Y Z P Q
end. 

Ltac rew_ifm_then_else_or_bol_bol_in_fst H1 :=
repeat match goal with 
|[ H : context [ ifb (ifb (Bvar ?n1) ?Y ?Z) ?P ?Q]   |- _ ] =>  ifm_then_else_or_bol_bol_fst_in n1 Y Z P Q H1
end. 

(********************IFM_THEN_ELSE_RPH***********Bool_Bool_snd*****************)

Ltac ifm_then_else_or_bol_bol_snd n1 n2 b1 b2 b3  := pose proof(IFM_THEN_ELSE_ORPH_B1 n1 n2 b1 b2 b3 );
match goal with
| [H : _ |- ?X ## ?Y ] =>    simpl in H ; match goal with | [H : ?X ## ?Y |- _ ] =>   rewrite H; clear H end
         end.

Ltac ifm_then_else_or_bol_bol_snd_in  n1 n2 b1 b2 b3  H1 := pose proof(IFM_THEN_ELSE_ORPH_B1 n1 n2 b1 b2 b3 );
match goal with
| [H : ?X ## ?Y |- _ ] =>    simpl in H ; match goal with | [H : ?X ## ?Y |- _ ] =>   rewrite H in H1; clear H end
   end.

Ltac rew_ifm_then_else_or_bol_bol_snd :=
repeat match goal with 
|[ H : _ |-  context [ ifb (Bvar ?n1) (ifb (Bvar ?n2) ?B1 ?B2) ?B3 ]  ] =>  ifm_then_else_or_bol_bol_snd n1 n2 B1 B2 B3
end. 

Ltac rew_ifm_then_else_or_bol_bol_in_snd H1 :=
repeat match goal with 
|[ H : context [ (ifb (Bvar ?n1) (ifb (Bvar ?n2) ?B1 ?B2) ?B3)]   |- _ ] =>  ifm_then_else_or_bol_bol_snd_in n1 n2 B1 B2 B3 H1
end. 

(**************************************recent***************Testing************)
(**********************************tactics to apply if b is same on both sides**********)

Ltac aply_breq :=
match goal with
| [|- (ifm_then_else_ ?B ?X1 ?Y1) # (ifm_then_else_ ?B ?X2 ?Y2) ] =>  apply breq_msgeq'; simpl; redg; try reflexivity
end.

Ltac aply_breq_same :=
match goal with
| [|- (ifm_then_else_ ?B ?X ?Y1) # (ifm_then_else_ ?B ?X ?Y2) ] =>  apply breq_msgeq1'; simpl
end.

(********************************three sessions 1 2 3 *************************)
(******************tactics to make (to x) = j is false if (to x) = i is true where i <> j *********)
Ltac false_to_sesns n  := 
match goal with 
| [|- (ifm_then_else_ (eqm ?X (i ?N)) ?X1 ?Y1) #  (ifm_then_else_ (eqm ?X (i ?N)) ?X2 ?Y2) ] => assert (beq_nat N n =false) ; try reflexivity ;
match goal with 
| [H: beq_nat ?N ?N2 = false |- _ ] => 
  apply IFEVAL_M''' with (x:= X ) (n1:= N) (n2:= N2) (t1 := X1) (t2:= Y1) in H; rewrite H; clear H end; assert (beq_nat N n =false) ; try reflexivity ;
match goal with 
| [H: beq_nat ?N ?N2 = false |- _ ] => 
  apply IFEVAL_M''' with (x:= X ) (n1:= N) (n2:= N2) (t1 := X2) (t2:= Y2) in H; rewrite H; clear H end
end.

Ltac  false_to_sesns_all := try false_to_sesns 1; try false_to_sesns 2; try false_to_sesns 3.

(******************************************************************************)
(*************apply andB elm ****************)

Ltac aply_andB_elm := 
match goal with 
|[|- context[ifm_then_else_ (ifb ?B1 ?B2 FAlse) ?T1 ?T2 ] ] => rewrite andB_elm' with (b1:= B1) (b2:= B2) (x:= T1) (y:= T2)
end.


 *)

(** New tactics *)


(** * Axioms and Definitions *)
Ltac funappmconst t H := apply FUNCApp_mconst with (m:= t) in H; simpl in H.

Ltac funappbconst b1 H := apply FUNCApp_bconst with (b:= b1) in H; simpl in H.

Ltac funappf1 f1 n H:= apply FUNCApp_f1 with (f:= f1) (p:= n) in H; simpl in H.

Ltac funappf2mb f1 n1 n2 H:= apply FUNCApp_f2b with (f:= f1) (p1:= n1) (p2:= n2) in H; simpl in H.

Ltac funappf2m f1 n1 n2 H:= apply FUNCApp_f2m with (f:= f1) (p1:= n1) (p2:= n2) in H; simpl in H.

Ltac funappf3mb f1 n1 n2 n3 H:= apply FUNCApp_f3b with (f:= f1) (p1:= n1) (p2:= n2) (p3:= n3) in H; simpl in H.

Ltac funappf3m f1 n1 n2 n3 H:= apply FUNCApp_f3m with (f:= f1) (p1:= n1) (p2:= n2) (p3:= n3) in H; simpl in H.

Ltac funappf4mb f1 n1 n2 n3 n4 H:= apply FUNCApp_f4mb with (f:= f1) (p1:= n1) (p2:= n2) (p3:= n3) (p4:= n4) in H; simpl in H.

Ltac funappf4m f1 n1 n2 n3 n4 H:= apply FUNCApp_f4m with (f:= f1) (p1:= n1) (p2:= n2) (p3:= n3) (p4:= n4) in H; simpl in H.

Ltac funappifm_then_else_  n1 n2 n3 H:= apply FUNCApp_f3bm with (f:= ifm_then_else_) (p1:= n1) (p2:= n2) (p3:= n3) in H; simpl in H.

Ltac funappifb  n1 n2 n3 H:= apply FUNCApp_g3 with (f:= ifb_then_else_) (p1:= n1) (p2:= n2) (p3:= n3) in H; simpl in H.

Ltac funappf2b f1 n1 n2 H:= apply FUNCApp_f1 with (f:= f1 ) (p1 := n1 ) (p2:= n2) in H; simpl in H.

Ltac retmylis H :=
  match goal with
    |[H: ?X ~ _  |- _ ] => pose (l := X)
  end.

Ltac funappeltPos2 tac f x y l H :=  retmylis H; tac f (eltPos x l) (eltPos y l) H; clear l.

Ltac funappeltPos3 tac x y z l H :=  tac  (eltPos x l) (eltPos y l) (eltPos z l) H; clear l.
  
Ltac aplyProjList l H1 :=
  match l with
    | [] => idtac
    | ?h :: ?t =>  simpl in H1; apply RESTR_proj with (p:= h) in H1; try reflexivity; unfold proj_at_pos in H1; simpl in H1; 
                    aplyProjList t H1; try reflexivity
  end.
(** Projection n times *)
Ltac aplyprojn n n' H:=
  match n with
    | 0 => idtac
    | S ?n'' => aplyProjList  [n'] H; simpl in H; aplyprojn n'' n' H; try reflexivity
  end.
 (*
 Fixpoint checkostmylis (t:oursum) {m} (l: mylist m):bool :=
  match l with
    | [] => true
    |  h::t' => (orb (oursum_beq t h) (checkostmylis t t'))
  end.

Fixpoint checksublis {m} (l: mylist m) {n} (l':mylist n) : bool :=
match (leb m n) , l with
  | true , [] => true
  | true , h :: t => if (checkostmylis h l') then (checksublis t l')
                     else false
  | _ , _ => false
end.

                    
 Fixpoint sublisIndcs {m} {n} (l :mylist m) (l': mylist n) : ilist nat m :=
  match  l with
    | [] => []
    | h :: t => (eltPos h l') :: (sublisIndcs t l')
  end.

 *)

Fixpoint checksublis {m} (l: mylist m) {n} (l':mylist n) : bool :=
match (leb m n) , l with
  | true , [] => true
  | true , h : t => if (checkmtmylis (ostomsg h) l') then (checksublis t l')
                     else false
  | _ , _ => false
end.

                    
Fixpoint sublisIndcs {m} {n} (l :mylist m) (l': mylist n) : ilist nat m :=
  match  l with
    | [] => []
    | h : t => (eltPos h l') : (sublisIndcs t l')
end.

 
 Axiom restr_sublis : forall {m} {n} (l1 l2 : mylist m) (l1' l2': mylist n) ,  l1 ~ l2 -> (andb (checksublis l1' l1) (checksublis l2' l2)  = true ) -> (sublisIndcs l1' l1) = (sublisIndcs l2' l2)-> l1' ~ l2'.

 Ltac restrsublis H :=
   match goal with
     | [|- ?X ~ ?Y] => apply restr_sublis with (l1':= X) (l2':=Y) in H; simpl in H
   end.

 (** Tactics *)


Definition topsymsg_beq (t t': message ) : bool :=
match t, t' with
| Mvar _, Mvar _  => true
| Mvar _, _  => false
| N _ , N _  => true
| N _ , _  => false                 
| ifm_then_else_ _ _ _,  ifm_then_else_ _ _ _ => true
| ifm_then_else_ _ _ _,  _ => false
| pair _ _ ,  pair _ _ => true
| pair _ _ ,   _  => false
| pi1 _ ,  pi1 _ => true
| pi1 _ ,  _ => false
| pi2 _ ,  pi2 _ => true
| pi2 _ ,   _ => false
| to _ , to _ => true
| to _ ,  _ => false
| z _ , z _ => true
| z _ ,  _ => false
| L _ , L _  => true
| L _ , _  => false                
| f _ , f _ => true
| f _ , _ => false
(* | f _ , _ => false *)
(** Attacker's computation *)
(** FOO symbols *)                   
(** Vote values *)
| V0 _ , V0 _ => true
| V0 _ ,  _ => false
| V1 _ , V1 _ => true
| V1 _ ,  _ => false
(** Public Key *)                    
| pubkey _, pubkey _ => true
| pubkey _, _ => false
(** Commitments *)
| kc _ , kc _ => true
| kc _ , _ => false
| comm  _ _ , comm _ _ => true
| comm  _ _ , _ => false
| open  _ _ _ , open _ _ _ => true
| open  _ _ _ , _ => false
(** Shuffling *)
| shufl _ _ _ , shufl _ _ _ => true
| shufl _ _ _ , _ => false
(** Encryptions *)
| ke _ , ke _ => true
| ke _ , _ => false
| re _ , re _ => true
| re _ , _ => false
| enc _ _ _, enc _ _ _ => true
| enc _ _ _, _ => false
| dec _ _ , dec _ _  => true
| dec _ _ ,  _  => false
(** Blind Signatures *)
| kb _ , kb _ => true
| kb _ , _ => false
| rb _ , rb _ => true
| rb _ ,  _ => false
| bsign _ _ _ , bsign _ _ _ => true
| bsign _ _ _ ,  _ => false
| bl _ _ _ , bl _ _ _ => true
| bl _ _ _ , _ => false
| ub _ _ _ _, ub _ _ _ _ => true
| ub _ _ _ _, _ => false
(** Signatures *)
| ks _ , ks _ => true
| ks _ ,  _ => false
| rs _ , rs _ => true
| rs _ , _ => false
| sign _ _ _ , sign _ _ _ => true
| sign _ _ _ ,  _ => false
| _ , _ => message_beq t t'
end.
                       

 Definition topsybol_beq (b b' : Bool):bool :=
   match b, b' with
     | Bvar _, Bvar _ =>  true
     | eqb  _ _ , eqb _ _  =>  true
     | eqm _ _, eqm _ _ =>  true
     | ifb_then_else_ _ _ _,  ifb_then_else_ _ _ _ => true
     | ver _ _ _, ver _ _ _ => true
     | bver _ _ _, bver _ _ _ => true
     | acc _ _ _ _, acc _ _ _ _  =>true
     | Bvar _, _ =>  false
     | eqb  _ _, _  =>  false
     | eqm _ _, _ =>  false
     | ifb_then_else_ _ _ _,  _ => false
     | ver _ _ _,  _ => false
     | bver _ _ _, _ => false
     | acc _ _ _ _, _  =>false
     | _ , _ => Bool_beq b b'
   end.


Definition topsyos_beq (t1 t2 : oursum): bool :=
  match t1 , t2 with
      | msg t1', msg t2' => topsymsg_beq t1' t2'
      | bol b1, bol b2 => topsybol_beq b1 b2
      | _ , _ => false
  end.

 
Fixpoint eltPos' (x:oursum) {n} (l:mylist n) :nat :=
  match l with
    | [] => 0
    | h:t =>  if  (oursum_beq x h)  then 1 else S (eltPos x t)
  end.
Fixpoint checkostmylis (x:oursum) {n} (l:mylist n) : bool :=
  match l with
    | [] => false
    | h : t => if (oursum_beq x h) then true else (checkostmylis x t)
  end.

Fixpoint checksublis'  (l: list oursum) {n} (l':mylist n) : bool :=
match (leb n n) , l with
  | true , nil => true
  | true , cons h t => if (checkostmylis h  l') then (checksublis' t l')
                     else false
  | _ , _ => false
end.

                    
 Fixpoint  sublisIndcs'  {n} (l :list oursum) (l': mylist n) : list nat :=
  match  l with
    | nil => nil
    | cons h t => cons (eltPos h l')  (sublisIndcs' t l')
  end.


Check subtrmls.
 Section subtrm'.
Variable f: message -> list oursum.
Fixpoint mapsubtrmls (l: list message) : list oursum :=
  match l with
    | nil => nil
    | cons h t => (app (f h) (mapsubtrmls t))
  end.
Fixpoint listm_listos (l: Mlist): oslist :=
  match l with
  | nil => nil
  | cons h t => (cons (msg h) (listm_listos t))
  end.
 End subtrm'.
 Eval compute in rb.
Fixpoint subtrmls_bol''(t: Bool) : list oursum :=
  match t with 
    | eqb  b1 b2 =>  (app (subtrmls_bol'' b1) (subtrmls_bol'' b2) )
    | eqm t1 t2 => (app (subtrmls_msg'' t1) (subtrmls_msg'' t2) )
    | ifb_then_else_ t1 t2 t3 => (app (subtrmls_bol'' t1) (app (subtrmls_bol'' t2) (subtrmls_bol'' t3)))
    | ver t1 t2 t3 => (app (subtrmls_msg'' t1) (app (subtrmls_msg'' t2) (subtrmls_msg'' t3)))
    | bver t1 t2 t3 => (app (subtrmls_msg'' t1) (app (subtrmls_msg'' t2) (subtrmls_msg'' t3)))
    | acc t1 t2 t3 t4 => (app (subtrmls_msg'' t1) (app (subtrmls_msg'' t2) (app (subtrmls_msg'' t3) (subtrmls_msg'' t4))))
    | _ => nil
 end
with subtrmls_msg'' (t:message) : list oursum :=
       match t with 
         | ifm_then_else_ b3 t1 t2 => (app (subtrmls_bol'' b3) (app (subtrmls_msg'' t1) (subtrmls_msg'' t2))) 
         | (Mvar n') => (cons (msg (Mvar n')) nil)
         | O => (cons (msg O) nil)
         | N n'=> (cons (msg (N n')) nil)
         | pair t1 t2 =>  (app (subtrmls_msg''  t1) (subtrmls_msg'' t2) )
         | pi1 t1 => match t1 with
                     | ke _ => (cons (msg (pi1 t1)) nil)
                     | kb _ => (cons (msg (pi1 t1)) nil)
                     | ks _ => (cons (msg (pi1 t1)) nil)
                     | _ => nil
                     end
         | pi2 t1 => match t1 with
                     | ke _ => (cons (msg (pi2 t1)) nil)
                     | kb _ => (cons (msg (pi2 t1)) nil)
                     | ks _ => (cons (msg (pi2 t1)) nil)
                     | _ => nil
                     end
         | to t1 =>  (subtrmls_msg'' t1)
         | L t1 =>  (subtrmls_msg'' t1)
         | f l =>  (listm_listos l)
         | ONE => (cons (msg ONE) nil)
         | TWO => (cons (msg TWO) nil)
         | THREE => (cons (msg THREE) nil)
         | A => (cons (msg A) nil)
         | B => (cons (msg B) nil)
         | M => (cons (msg M) nil)
         | C1 => (cons (msg C1) nil)
         | C2 => (cons (msg C2) nil)
         | C3 => (cons (msg C3) nil)
         | V0 t1 => (subtrmls_msg'' t1)
         | V1 t1 => (subtrmls_msg'' t1)
         | pubkey t1 => (subtrmls_msg'' t1)
         | kc t1 => nil
         | comm t1 t2 => (cons (msg (comm t1 t2)) nil)
         | open t1 t2 t3 => (app (subtrmls_msg'' t1) (app (subtrmls_msg'' t2) (subtrmls_msg'' t3)))
         | shufl t1 t2 t3 => (app (subtrmls_msg'' t1) (app (subtrmls_msg'' t2) (subtrmls_msg'' t3)))     
         | re t1 =>  (cons (msg (re t1)) nil)
         | ke t1 =>  nil
         | enc t1 t2 t3 => (app (subtrmls_msg'' t1) (app (subtrmls_msg'' t2) (subtrmls_msg'' t3)))
         | dec t1 t2 =>  (app (subtrmls_msg'' t1) (subtrmls_msg'' t2))
         | bot => (cons (msg bot) nil)
         | kb t1 =>  nil
         | rb t1 =>  (cons (msg (rb t1)) nil)
         | bsign t1 t2 t3 => (app (subtrmls_msg'' t1) (app (subtrmls_msg'' t2) (subtrmls_msg'' t3)))
         | bl t1 t2 t3 => (app (subtrmls_msg'' t1) (app (subtrmls_msg'' t2) (subtrmls_msg'' t3)))
         | ub t1 t2 t3 t4 =>  (app (subtrmls_msg'' t1) (app (subtrmls_msg'' t2) (app (subtrmls_msg'' t3) (subtrmls_msg'' t4))))
         | ks t1 =>  nil
         | rs t1 =>  (cons (msg (rs t1)) nil)
         | z t1 => (cons (msg (z t1)) nil)
         | sign t1 t2 t3 => (app (subtrmls_msg'' t1) (app (subtrmls_msg'' t2) (subtrmls_msg'' t3)))
       end.


(** Subterms of [oursum] term. *)

Definition subtrmls_os'' (t:oursum) : list oursum :=
  match t with 
    | msg t1 => subtrmls_msg'' t1
    | bol b1 =>  subtrmls_bol'' b1
  end.

(** Subterms of terms of type [mylist n] for some [n].*)

Fixpoint subtrmls_mylis'' {n} (l:mylist n) : list oursum :=
  match l with 
    | [] => nil
    | h: t => (app (subtrmls_os'' h) (subtrmls_mylis'' t))
  end.
  
 
(** Tactics *)
 

Axiom funapptrm : forall {m} (m1 m2 : oursum) (l1 l2 : mylist m),  l1 ~ l2 -> (topsyos_beq m1 m2 = true ) -> (andb (checksublis' (subtrmls_os'' m1)  l1) (checksublis' (subtrmls_os'' m2) l2) = true) ->  (sublisIndcs' (subtrmls_os'' m1) l1) = (sublisIndcs' (subtrmls_os'' m2) l2) -> (l1 ++ [m1]) ~ (l2 ++ [m2]).


Ltac funapptrmhyp s1 s2 H :=
  apply funapptrm with (m1 := s1) (m2 := s2) in H; simpl in H.
 

(** keep the blind term as it is **)

Fixpoint subtrmlsbl_bol(t: Bool) : list oursum :=
  match t with 
    | eqb  b1 b2 =>  (app (subtrmlsbl_bol b1) (subtrmlsbl_bol b2) )
    | eqm t1 t2 => (app (subtrmlsbl_msg t1) (subtrmlsbl_msg t2) )
    | ifb_then_else_ t1 t2 t3 => (app (subtrmlsbl_bol t1) (app (subtrmlsbl_bol t2) (subtrmlsbl_bol t3)))
    | ver t1 t2 t3 => (app (subtrmlsbl_msg t1) (app (subtrmlsbl_msg t2) (subtrmlsbl_msg t3)))
    | bver t1 t2 t3 => (app (subtrmlsbl_msg t1) (app (subtrmlsbl_msg t2) (subtrmlsbl_msg t3)))
    | acc t1 t2 t3 t4 => (app (subtrmlsbl_msg t1) (app (subtrmlsbl_msg t2) (app (subtrmlsbl_msg t3) (subtrmlsbl_msg t4))))
    | _ => nil
 end
with subtrmlsbl_msg (t:message) : list oursum :=
       match t with 
         | ifm_then_else_ b3 t1 t2 => (app (subtrmlsbl_bol b3) (app (subtrmlsbl_msg t1) (subtrmlsbl_msg t2))) 
         | (Mvar n') => (cons (msg (Mvar n')) nil)
         | O => (cons (msg O) nil)
         | N n'=> (cons (msg (N n')) nil)
         | pair t1 t2 =>  (app (subtrmlsbl_msg  t1) (subtrmlsbl_msg t2) )
         | pi1 t1 => match t1 with
                     | ke _ => (cons (msg (pi1 t1)) nil)
                     | kb _ => (cons (msg (pi1 t1)) nil)
                     | ks _ => (cons (msg (pi1 t1)) nil)
                     | _ => nil
                     end
         | pi2 t1 => match t1 with
                     | ke _ => (cons (msg (pi2 t1)) nil)
                     | kb _ => (cons (msg (pi2 t1)) nil)
                     | ks _ => (cons (msg (pi2 t1)) nil)
                     | _ => nil
                     end
         | to t1 =>  (subtrmlsbl_msg t1)
         | L t1 =>  (subtrmlsbl_msg t1)
         | f l =>  (listm_listos l)
         | ONE => (cons (msg ONE) nil)
         | TWO => (cons (msg TWO) nil)
         | THREE => (cons (msg THREE) nil)
         | A => (cons (msg A) nil)
         | B => (cons (msg B) nil)
         | M => (cons (msg M) nil)
         | C1 => (cons (msg C1) nil)
         | C2 => (cons (msg C2) nil)
         | C3 => (cons (msg C3) nil)
         | V0 t1 => (subtrmlsbl_msg t1)
         | V1 t1 => (subtrmlsbl_msg t1)
         | pubkey t1 => (subtrmlsbl_msg t1)
         | kc t1 => nil
         | comm t1 t2 => (cons (msg (comm t1 t2)) nil)
         | open t1 t2 t3 => (app (subtrmlsbl_msg t1) (app (subtrmlsbl_msg t2) (subtrmlsbl_msg t3)))
         | shufl t1 t2 t3 => (app (subtrmlsbl_msg t1) (app (subtrmlsbl_msg t2) (subtrmlsbl_msg t3)))     
         | re t1 =>  (cons (msg (re t1)) nil)
         | ke t1 =>  nil
         | enc t1 t2 t3 => (app (subtrmlsbl_msg t1) (app (subtrmlsbl_msg t2) (subtrmlsbl_msg t3)))
         | dec t1 t2 =>  (app (subtrmlsbl_msg t1) (subtrmlsbl_msg t2))
         | bot => (cons (msg bot) nil)
         | kb t1 =>  nil
         | rb t1 =>  (cons (msg (rb t1)) nil)
         | bsign t1 t2 t3 => (app (subtrmlsbl_msg t1) (app (subtrmlsbl_msg t2) (subtrmlsbl_msg t3)))
         | bl t1 t2 t3 => (cons (msg (bl t1 t2 t3)) nil) 
         | ub t1 t2 t3 t4 =>  (app (subtrmlsbl_msg t1) (app (subtrmlsbl_msg t2) (app (subtrmlsbl_msg t3) (subtrmlsbl_msg t4))))
         | ks t1 =>  nil
         | rs t1 =>  (cons (msg (rs t1)) nil)
         | z t1 => (cons (msg (z t1)) nil)
         | sign t1 t2 t3 => (app (subtrmlsbl_msg t1) (app (subtrmlsbl_msg t2) (subtrmlsbl_msg t3)))
       end.


(** Subterms of [oursum] term. *)

Definition subtrmlsbl_os (t:oursum) : list oursum :=
  match t with 
    | msg t1 => subtrmlsbl_msg t1
    | bol b1 =>  subtrmlsbl_bol b1
  end.


Axiom funapptrmbl : forall {m} (m1 m2 : oursum) (l1 l2 : mylist m),  l1 ~ l2 -> (topsyos_beq m1 m2 = true ) -> (andb (checksublis' (subtrmlsbl_os m1)  l1) (checksublis' (subtrmlsbl_os m2) l2) = true) ->  (sublisIndcs' (subtrmlsbl_os m1) l1) = (sublisIndcs' (subtrmlsbl_os m2) l2) -> (l1 ++ [m1]) ~ (l2 ++ [m2]).


Ltac funapptrmhypbl s1 s2 H :=
  apply funapptrmbl with (m1 := s1) (m2 := s2) in H; simpl in H.