Require Export prop_16.

(** The following theorem states that [x~f -> x=f] *)
(* TODO: XXX bring this from the machine checked proofs of the ACM paper  *)
Axiom Example10_B: forall (x  F z : Bool), [bol x] ~ [bol (const F z )] ->  x ## (const F  z).
Axiom beq_nat_sym: forall n m: nat, (n =? m)%nat = (m =? n)%nat.
Axiom clos_name_do_not_occur: forall n t, ^? t = true -> occur_name_msg n t = false.


(** Unforgeability of a commitment key presented in Proposition 11 of the JCS submission *)
Proposition unforgeCommitKey: forall n t t1, beq_nat n 4 = false -> Fresh (cons n nil) [msg t] = true ->
                                             closMsg t = true ->
                                             (length (mVarMsg t1) <=? 1)%nat = true ->
                                             mVarMsg t1 = (cons n nil) ->
                                             t #? O = FAlse ->
                                             let k := (kc (nonce n)) in
                                             let c := (comm t k) in
                                             ({{n := c}} t1) #? k ## FAlse.
Proof.  intros.
        pose proof(compHid_latest n n O t (compl t) [msg t, msg (compl t)]).
        repeat rewrite complEql in H5. repeat rewrite IFTRUE_M in H5.
        assert(assumption_H3: closMylist [msg O, msg t, msg (compl t)] = true /\
                              closMylist [msg t, msg (compl t)] = true /\
                              Fresh (n ::nil) ([msg O, msg t, msg (compl t), msg t, msg (compl t)]) = true /\
                              Fresh (n ::nil) ([msg O, msg t, msg (compl t), msg t, msg (compl t)]) = true).
        simpl. rewrite H1. simpl. simpl. 
        unfold Fresh. simpl. unfold Fresh in H0. simpl in H0.
        assert (occur_name_msg n t = false).
        destruct (occur_name_msg n t).
        simpl in H0. inversion H0.
        Require Import Bool.
        rewrite andb_false_r. reflexivity. reflexivity.
        rewrite H6.
        simpl.
        rewrite H6 in H0; auto.
        (* rewrite H6. simpl. *)
        apply H5 in assumption_H3.
        simpl in assumption_H3.
        (** apply funcApp with pi1 *)
        funappf1 pi1 3 assumption_H3.
        repeat rewrite proj1 in assumption_H3.

        (** apply RESTR **)
        restr_proj_in 4 assumption_H3.

        (** apply FuncApp for submsg_msg **)
        apply funcApp_latest with (p:= 1) (n:= n) (t:=t1) in assumption_H3.
        simpl in assumption_H3.
        Ltac funapp_f2m_new_in g n1 n2 H:= apply FUNCApp_f2m with (f := g) (p1:= n1) (p2:= n2) in H ; simpl in H.
        funapp_f2m_new_in comm 2 4 assumption_H3.
        funapp_eqm_in 2 1 assumption_H3.
        do 5 dropLast_in assumption_H3.

        (** Prove RHS of formula 1 reduces to false *)
        assert((comm (compl t) (fooAxioms.k n)) #?
                     (comm t {{n := comm (compl t) (fooAxioms.k n)}} (t1)) ## FAlse).
        rewrite <- compBind.
        apply Msgneql in H1.
        rewrite H4 in H1. red_in H1. rewrite Example14_M' in H1.
        rewrite H1. redg. reflexivity. rewrite H6 in assumption_H3.

        (* Prove (t1[c1] #? (kc n)) ## FAlse *)
        rewrite <- IFTFb.
        assert( c #? c ## TRue).
        apply EQmsg. reflexivity.
        rewrite <- H7.
        unfold c at 3.
        pose proof(eqbrmsg_bol ((Mvar 4) #? (comm t (Mvar 0))) FAlse 1 2 0).
        simpl in H8.
        Require Export prop_13.
        inversion H1.
        apply sub_clos with (n:=0) (s:= (Mvar 1)) in H1.
        rewrite H1 in H8.
        inversion H10.
        apply sub_clos with (n:=0) (s:= (Mvar 2)) in H10.
        rewrite H10 in H8.
        apply Forall_ELM_EVAL_B3 with (n:= 2) (b:= k) in H8.
        simpl in H8.
        inversion H11.
        apply sub_clos with (n:=2) (s:= k) in H11.
        repeat rewrite H11 in H8.
        apply Forall_ELM_EVAL_B3 with (n:= 1) (b:= ({{n := c}} (t1))) in H8.
        simpl in H8.
        inversion H12.
        apply sub_clos with (n:= 1) (s:= ({{n := c}} (t1))) in H12.
        repeat rewrite H12 in H8.
        apply Forall_ELM_EVAL_B3 with (n:= 4) (b:= c) in H8.
        simpl in H8.
        inversion H13.
        apply sub_clos with (n:= 4) (s:= c) in H13.
        repeat rewrite H13 in H8.
        rewrite single_var_sub in H8.
        unfold k.
        rewrite <- H8.
        apply Example10_B with (z:= FAlse) in assumption_H3.
        unfold const in assumption_H3.
        unfold c.
        unfold k.
        unfold fooAxioms.k in assumption_H3.
        rewrite assumption_H3.
        redg.
        reflexivity; try auto.
        rewrite beq_nat_sym; auto. auto. auto. simpl. rewrite H.
        apply clos_name_do_not_occur with (n:=4) in H14.
        rewrite H14; try auto.
        auto. auto. Qed.
