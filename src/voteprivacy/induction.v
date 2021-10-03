Require Export cpdtTactics.


  Axiom f_cong2: forall l1 l2, (f l1) # (f l2) -> l1 = l2.
Lemma InvarMsg: forall (m:message), (submsg_msg 0 (Mvar 0) m) # m.
Proof.  induction m using (message_Bool_ind') with (P:= (fun m => (submsg_msg 0 (Mvar 0) m) # m)) (P0:= (fun b =>  ((submsg_bol 0 (Mvar 0) b) ## b)));crush.
destruct n.
reflexivity.
reflexivity.
induction l.
simpl. reflexivity.
simpl in H |- *.
inversion H.
rewrite H0.
simpl in IHl |- *.
apply IHl in H1.

simpl.
apply f_cong2 in H1.
rewrite H1. 
reflexivity. Qed.
Lemma invarm : forall  (m:message), m # m.
  
Proof. induction m using (message_Bool_ind') with (P:= (fun m => m # m)) (P0:= (fun b =>  b##b));crush. Qed.

Lemma invarb: forall (b:Bool), b##b.
 Proof. induction b using (Bool_message_ind') with (P:= (fun m => m # m)) (P0:= (fun b =>  b##b));crush. Qed.

Set Nested Proofs Allowed.

Ltac rewriteHyp :=
  match goal with
    | [ H : _ |- _ ] =>  rewrite H by solve [ auto ]
  end.
Ltac un_done :=
  repeat match goal with
           | [ H : done _ |- _ ] => clear H
         end.
  
                                                                                         
 
Lemma  invarsub_Bmsg : forall (t:message), ((0:= (Bvar 0))t  # t).

Proof.
 induction t using (message_Bool_ind') with (P:= (fun m => (subbol_msg 0 (Bvar 0) m) # m)) (P0:= (fun b =>  ((subbol_bol 0 (Bvar 0) b) ## b))); crush. 
induction l.
simpl. reflexivity.
simpl.
simpl in H; inversion H.
apply IHl in H1.
apply f_cong2 in H1.
rewrite H1, H0; reflexivity.
induction n. reflexivity.
simpl.
reflexivity. Qed.
Lemma invarsub_b: forall b, (([0:=(Bvar 0)] b) ## b).
  Proof.
 induction b using (Bool_message_ind') with (P:= (fun m => (subbol_msg 0 (Bvar 0) m) # m)) (P0:= (fun b =>  ((subbol_bol 0 (Bvar 0) b) ## b))); crush.
induction l.
simpl. reflexivity.
simpl.
simpl in H; inversion H.
apply IHl in H1.
apply f_cong2 in H1.
rewrite H1, H0; reflexivity.
induction n. reflexivity.
simpl.
reflexivity. Qed.

  