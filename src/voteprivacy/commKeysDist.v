Require Export lemma_25.

Section auxLemmas.
  Lemma n_neq_np1: forall n, (n + 1 =? n)%nat = false.
  Proof. intros.
         induction n.
         reflexivity.
         auto.
  Qed.

  Lemma n_neq_npc: forall n c, (c =? 0)%nat = false -> (n + c =? n)%nat = false.
  Proof. intros.
         induction n.
         simpl.
         destruct c.
         repeat (try inversion H; try auto).
         reflexivity.
         simpl. auto.
  Qed.

  Lemma one_plus_not_zero: forall n, (1 + n =? 0)%nat = false.
  Proof. induction n; auto. Qed.

  Axiom eqmSym: forall x y, (x #? y) ## (y #? x).
End auxLemmas.

Proposition commKeysDist: forall n1 n2, (n1 =? n2 = false)%nat -> let k1:= kc (nonce n1) in
                                                    let k2:= kc (nonce n2) in
                                                    k1 #? k2 ## FAlse.
Proof. intros.
       pose proof(let c1:= (n1+n2+1) in
                  let c2:= 2*c1 in
                  let nonce:= nonce c2 in
                  compHid n1 c1 |_ nonce (compl nonce) [msg nonce, msg k2]).
       pose proof(complEql (nonce (2*(n1+n2+1)))).
       simpl in H0. rewrite H1 in H0; repeat try rewrite IFTRUE_M in H0.
       funappf2m comm 1 2 H0.
       (* funapptrmhypbl (let c1:= (n1+n2+1) in *)
       (*                 let c2:= 2*c1 in *)
       (*                 msg (comm (nonce c2) k2)) (let c1:= (n1+n2+1) in *)
       (*                                            let c2:= 2*c1 in *)
       (*                                            msg (comm (nonce c2) k2)) H0. *)
       do 2 restr_proj_in 2 H0.
       funappf1 pi1 2 H0.
       repeat rewrite proj1 in H0.
       restr_proj_in 3 H0.
       funappf2mb eqm 1 2 H0.
       restr_proj_in 3 H0.
       restr_proj_in 2 H0. 
       (* rewrite <- IFSAME_B with (b:= k1 #? k2) in H0. *)
       (* rewrite <- IFSAME_B with (b:= k1 #? k2) (b1:= (comm (compl (nonce (n1 + n2 + 1 + (n1 + n2 + 1 + 0)))) (k n1)) #? *)
       (*    (comm (nonce (n1 + n2 + 1 + (n1 + n2 + 1 + 0))) k2)) in H0. *)
       (* assert((|nonce (n1 + n2 + 1 + (n1 + n2 + 1 + 0))| #? |nonce (n1 + n2 + 1 + (n1 + n2 + 1 + 0))|) ## TRue). *)
       unfold k in H0.
       fold k1 in H0.
       rewrite <- compBind with (t1:= (compl (nonce (n1 + n2 + 1 + (n1 + n2 + 1 + 0))))) (t2:= nonce (n1 + n2 + 1 + (n1 + n2 + 1 + 0))) in H0.
       pose proof(Msgneql (nonce (n1 + n2 + 1 + (n1 + n2 + 1 + 0)))).
       pose proof (FRESHNEQ (n1 + n2 + 1 + (n1 + n2 + 1 + 0)) O).
       Search "const".
       apply consteql with (x:= (nonce (n1 + n2 + 1 + (n1 + n2 + 1 + 0))) #? O) (f:= FAlse) in H3; try auto.
       rewrite H3 in H2; try red_in H2.
       rewrite eqmSym in H2.
       rewrite H2 in H0.
       red_in H0.
       apply consteql in H0; try auto.
       rewrite <-IFTFb.
       assert((comm (nonce (n1 + n2 + 1 + (n1 + n2 + 1 + 0))) k2) #?
       (comm (nonce (n1 + n2 + 1 + (n1 + n2 + 1 + 0))) k2) ## TRue).
       rewrite eqmeql; try reflexivity.
       rewrite <- H4.
       Search "eqbr".
       pose proof(eqbrmsg_msg'' (Mvar 20) k1 k2 (comm (nonce (n1 + n2 + 1 + (n1 + n2 + 1 + 0))) (Mvar 20)) #?
           (comm (nonce (n1 + n2 + 1 + (n1 + n2 + 1 + 0))) k2) FAlse).
       simpl in H5. fold k2.
       fold k2 in H5.
       rewrite <- H5.
       rewrite H0; redg.
       repeat try reflexivity.
       reflexivity.
       split; try auto.
       unfold Fresh; try reflexivity.
       simpl.
       unfold noDupNlist.
       simpl. 
       Search "eqb_refl".
       rewrite Nat.eqb_refl.
       reflexivity.
       repeat (split; try auto).
       simpl.
       unfold Fresh.
       simpl.
       rewrite <- plus_assoc.
       repeat rewrite n_neq_npc.
       rewrite <- plus_assoc.
       repeat rewrite n_neq_npc.
       simpl.
       rewrite Nat.eqb_sym.
       rewrite H.
       simpl.
       rewrite Nat.eqb_sym.
       rewrite plus_assoc.
       rewrite plus_comm with (m:= n2).
       rewrite <- plus_assoc.
       rewrite n_neq_npc.
       simpl.
       unfold noDupNlist.
       simpl.
       rewrite Nat.eqb_refl.
       rewrite plus_comm.
       rewrite <- plus_assoc.
       repeat rewrite n_neq_npc.
       rewrite Nat.eqb_refl.
       reflexivity.
       rewrite one_plus_not_zero; try auto.
       rewrite plus_comm; try rewrite one_plus_not_zero; try auto.
       rewrite plus_comm with (m:=1).
       rewrite <- plus_assoc.
       try rewrite one_plus_not_zero; try auto.
       rewrite plus_assoc.
       rewrite plus_comm with (m:=1).
       try rewrite one_plus_not_zero; try auto.
Qed.
        
