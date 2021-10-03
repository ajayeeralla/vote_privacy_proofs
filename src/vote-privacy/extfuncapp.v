 
(************************************************************************)
(* Copyright (c) 2017-2018, Ajay Kumar Eeralla <ae266@mail.missouri.edu>*)     
(************************************************************************)
     
Require Export voting_prop.
Require Import Coq.Bool.Bool.
Set Nested Proofs Allowed.

Axiom funcapp_fn2: forall n b b' x x' (z z':mylist n) f, (z ++ [bol b, msg x])~ (z' ++ [bol b', msg x']) -> (z ++ [bol b, msg x, msg (f z b x)]) ~ (z' ++ [bol b', msg x', msg (f z' b' x')]).
Axiom restr: forall n (l1 l1':mylist n) n' (l2 l2': mylist n'), (l1 ++ l2) ~ (l1' ++ l2') ->  forall m' (p: mylist n' -> mylist m'), m' <= n' ->  (l1 ++ (p l2))~ (l1' ++ (p l2')).
Variable A: Type.
Definition length : list A -> nat :=
  fix length l :=
  match l with
   | nil => 0
   | _ :: l' => S (length l')
  end.
Check Cons.
Fixpoint inject (ls : list A) : ilist A (length ls) :=
    match ls with
      | nil => (Nil A)
      | h :: t => Cons A _ h (inject t)
    end.
Fixpoint unject n (ls : ilist A n) : list A :=
    match ls with
      | Nil _ => nil
      | Cons _ _ h t => h :: unject _ t
    end.


 Theorem inject_inverse : forall ls, unject _ (inject ls) = ls.
    induction ls. reflexivity. simpl. rewrite IHls; reflexivity.
  Qed.
Lemma ind_mylist: forall n (z : mylist n), (reverse (reverse z)) = z.
Proof. intros. induction z. simpl. reflexivity. 
simpl. 
unfold app_elt_last.  Abort.

Axiom restr_in_list: forall n m m' (z z':mylist n) (z1 z1':mylist m), m <= m' -> (z ++ z1) ~ (z ++ z1') ->  forall (p: mylist m -> mylist m'), (z ++ (p z1)) ~ (z ++ (p z1')).
Axiom ifmf_listnbm: forall n (l:mylist n) b x y (f:mylist n -> Bool -> message -> message),
    (f l b (If b then x else y)) # (If b then (f l b x) else (f l b y)).
 Axiom funcapp_m_last: forall  {n n'} (m:message) (z z': mylist n) (z1 z1':mylist n'), (const_msg m = true) -> (z ++ z1) ~(z' ++ z1') -> (z ++ (z1 ++ [msg m])) ~ (z' ++ (z1' ++ [msg m])).
 Ltac funcapp_fm_last m' H := apply funcapp_m_last with (m:= m') in H; simpl in H.
 Axiom ind_assoc: forall {n1 n2 n3} (z z':mylist n1) (z1 z1': mylist n2) (z2 z2': mylist n3), ((z ++ z1) ++ z2) ~ ((z' ++ z1') ++ z2') -> (z ++ (z1 ++ z2)) ~ (z' ++ (z1' ++ z2')).
   Axiom funcapp_f3bm': forall {n n'} f p1 p2 p3 (z z':mylist n) (z1 z1':mylist n'), (z ++ z1) ~ (z' ++ z1') -> ((z ++ z1) ++ [msg (f (ostobol (getelt_at_pos p1 z1)) (ostomsg (getelt_at_pos p2 z1)) (ostomsg (getelt_at_pos p3 z1)))]) ~ ((z' ++ z1') ++ [msg (f (ostobol (getelt_at_pos p1 z1')) (ostomsg (getelt_at_pos p2 z1')) (ostomsg (getelt_at_pos p3 z1')))]).
Ltac funcapp_f3bm'_in f' n1 n2 n3 H:= apply funcapp_f3bm' with (f:= f') (p1:= n1) (p2:=n2) (p3:= n3) in H.
Lemma aply_ifeval: forall n t1 t2 t3, (If (Bvar n) then (If (Bvar n) then t1 else t2) else t3) # (If (Bvar n) then t1 else t3).
Proof. intros. rewrite IFEVAL_M. simpl. rewrite Nat.eqb_refl. rewrite IFTRUE_M. rewrite IFEVAL_M with (t2:= t3).
reflexivity.
Qed.

Lemma aply_ifeval_gen: forall b t1 t2 t3, (If b then (If b then t1 else t2) else t3) # (If b then t1 else t3).
Proof. intros. rewrite IFEVAL_M'. simpl.
       Axiom sub_b_true: forall b, (subbol_bol' b TRue b) ## TRue.
rewrite sub_b_true.
rewrite IFTRUE_M.
rewrite IFEVAL_M' with (t2:=t3); auto. reflexivity.
Qed.

Lemma extFuncapp: forall n b b' x x' y y' (z z': mylist n) (f : (mylist n) -> Bool -> message-> message), (z ++ [bol b, msg (If b then x else y)]) ~ (z' ++ [bol b', msg (If b' then x' else y')]) -> (z ++ [bol b, msg (If b then (f z b x) else |_)])~ (z' ++ [bol b', msg (If b' then (f z' b' x') else |_)]).


Proof. intros.
       apply funcapp_fn2 with (f:= f) in H.
       apply restr with (p:= droplastsec) in H. unfold droplastsec in H. simpl in H. 
       repeat rewrite ifmf_listnbm in  H.
       funcapp_fm_last |_ H.    
       apply funcapp_f3bm' with (f0:= (ifm_then_else_)) (p1:= 1) (p2:=2) (p3:=3) in H; unfold getelt_at_pos; simpl in H.
       simpl in H.
(********************)
       repeat rewrite aply_ifeval_gen in H.
       apply ind_assoc in H; simpl in H.
       apply restr with (p:= droplastsec) in H; unfold droplastsec in H; simpl in H.
       apply restr with (p:= droplastsec) in H; unfold droplastsec in H; simpl in H; auto.
       simpl.
       SearchAbout nat. apply le_S. reflexivity.
       reflexivity.
       simpl.
       apply le_S; reflexivity.
Qed.
