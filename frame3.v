
Load "foo_prot2".
 Section frame3.

 
(*******************************************************************************)
(* Theorem frame3ind : (phi3 0 1) ~ (phi3 1 0). 
Proof. repeat unf. unfold phi3. simpl. unfold t1, t2. unfold q1_s, q2_s, q3_s; repeat unf.
       unfold q11, q12, q13, q21, q22, q23, q31, q32.
       repeat unfold admin, achecks.
       ufcma_pi1 x1.  
ufcma_pi1 (x2t 0).
ufcma_pi2 (x2t 0).
ufcma_pi1 (x2ft 1). 
ufcma_pi2 (x2ft 0). 
ufcma_pi1 (x2t 1).
ufcma_pi2 (x2t 1).
ufcma_pi1 (x2ft 0).
repeat aply_andB_elm.  
rew_mupbver;aply_bver; rew_hyps; try split; try reflexivity.
rew_mupbver;aply_bver; rew_hyps; try split; try reflexivity.
rew_mupbver;aply_bver; rew_hyps; try split; try reflexivity.
rew_mupbver;aply_bver; rew_hyps; try split; try reflexivity.
ufcma_pi1 (x3tft 0 1).
ufcma_pi2 (x3tft 0 1).
ufcma_pi1 (x3ftt 1).
ufcma_pi1 (x3ftt 0).
ufcma_pi1 (x3ftft 0 1).
ufcma_pi2 (x3ftft 0 1).
rew_mupbver;aply_bver; rew_hyps; try split; try reflexivity.
rew_mupbver;aply_bver; rew_hyps; try split; try reflexivity.
rew_mupbver;aply_bver; rew_hyps; try split; try reflexivity.
rew_mupbver;aply_bver; rew_hyps; try split; try reflexivity.
rew_mupbver;aply_bver; rew_hyps; try split; try reflexivity.
rew_mupbver;aply_bver; rew_hyps; try split; try reflexivity.
rew_mupbver;aply_bver; rew_hyps; try split; try reflexivity.
rew_mupbver;aply_bver; rew_hyps; try split; try reflexivity.

rew_mupbver;aply_bver; rew_hyps; try split; try reflexivity.
rew_mupbver;aply_bver; rew_hyps; try split; try reflexivity.
rew_mupbver;aply_bver; rew_hyps; try split; try reflexivity.
rew_mupbver;aply_bver; rew_hyps; try split; try reflexivity.
(*
assert((ifb (eqm (pi1 (pi2 (pi1 (x3tft 0 1)))) (e (b 0 7) 8))
                     (ver (pk 1) (e (b 0 7) 8) (pi2 (pi2 (pi1 (x3tft 0 1)))))
                     FAlse) ## (eqm (pi1 (pi2 (pi1 (x3tft 0 1)))) (e (b 0 7) 8))).

Axiom eqbrmsg_bol :forall ( b1 b2: Bool) (n1 n2 n3 :nat ), (ifb (eqm  (Mvar n1)  (Mvar n2)) [[n3 := (Mvar n1)]]b1 b2) ## (ifb (eqm  (Mvar n1)(Mvar n2)) [[n3:= (Mvar n2)]] b1 b2). 
pose proof(  eqbrmsg_bol (ver (pk 1) (e (b 0 7) 8) (Mvar 2) ) FAlse 0 1 2). simpl in H. 
apply Forall_ELM_EVAL_B3 with (n:= 0) (b:= (pi1 (pi2 (pi1 (x3tft 0 1))))) in H. simpl in H.

apply Forall_ELM_EVAL_B3 with (n:= 1) (b:= (e (b 0 7) 8)) in H. simpl in H.
rewrite correctness with (n:= 1) (t:= (e (b 0 7) 8)) in H. *)
       apply IFBRANCH_M3 with (ml1:= phi0) (ml2:= phi0). simpl.
       apply IFBRANCH_M2 with (ml1:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8)))]) (ml2:=  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (e (b 1 7) 8)))]).
       simpl.
apply IFBRANCH_M1 with (ml1:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8)));
    bol (eqm (to (x2t 0)) (V 2));
    msg (pk 2, (e (b 1 11) 12, sign (sk 2) (e (b 1 11) 12)))]) (ml2:=  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (e (b 1 7) 8)));
   bol (eqm (to (x2t 1)) (V 2));
   msg (pk 2, (e (b 0 11) 12, sign (sk 2) (e (b 0 11) 12)))]). simpl.
ufcma_pi1 (x3tft 1 0).
ufcma_pi2 (x3tft 1 0).
apply IFBRANCH_M1 with (ml1:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8)));
    bol (eqm (to (x2t 0)) (V 2));
    msg (pk 2, (e (b 1 11) 12, sign (sk 2) (e (b 1 11) 12)));
    bol (eqm (to (x3tft 0 1)) (pk 3))]) (ml2:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (e (b 1 7) 8)));
   bol (eqm (to (x2t 1)) (V 2));
   msg (pk 2, (e (b 0 11) 12, sign (sk 2) (e (b 0 11) 12)));
   bol (eqm (to (x3tft 1 0)) (pk 3))]). simpl.
apply IFBRANCH_M1 with (ml1:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1));
    msg (pk 1, (e (b 0 7) 8, sign (sk 1) (e (b 0 7) 8)));
    bol (eqm (to (x2t 0)) (V 2));
    msg (pk 2, (e (b 1 11) 12, sign (sk 2) (e (b 1 11) 12)));
    bol (eqm (to (x3tft 0 1)) (pk 3));
    bol
      (ifb (eqm (pi1 (pi2 (pi1 (x3tft 0 1)))) (e (b 0 7) 8))
         (ver (pk 1) (e (b 0 7) 8) (pi2 (pi2 (pi1 (x3tft 0 1))))) FAlse)]) (ml2:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1));
   msg (pk 1, (e (b 1 7) 8, sign (sk 1) (e (b 1 7) 8)));
   bol (eqm (to (x2t 1)) (V 2));
   msg (pk 2, (e (b 0 11) 12, sign (sk 2) (e (b 0 11) 12)));
   bol (eqm (to (x3tft 1 0)) (pk 3));
   bol
     (ifb (eqm (pi1 (pi2 (pi1 (x3tft 1 0)))) (e (b 1 7) 8))
        (ver (pk 1) (e (b 1 7) 8) (pi2 (pi2 (pi1 (x3tft 1 0))))) FAlse)]). simpl. 
aply_blindness 3 8 12 0 1 (b 0 7) (b 1 11)  ((Mvar 0), (Mvar 1)) ((Mvar 0), (Mvar 1))  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                                                       msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); msg (sk 3) ] .
aplyprojn 1 16 H; try split; try reflexivity.
rep_commits 0 1 11 21 7 22 fr1 fr2 temp H H0.
rename H0 into H.
appconst H. 
x1checks x1 x1 H. 
funapp_vtrm 1 0 1 7 8 H.
x1checks (x2t 0 ) (x2t 1) H.
funapp_vtrm 2 1 0 11 12 H.
x1checks (x3tft 0 1) (x3tft 1 0) H.
adminchecks (x3tft 0 1) (x3tft 1 0) H.
ver_suc 1 (pi1 (x3tft 0 1)) (e (b 0 7) 8) (pi1 (x3tft 1 0)) (e (b 1 7) 8) H.
ver_suc 2 (pi2 (x3tft 0 1)) (e (b 1 11) 12) (pi2 (x3tft 1 0)) (e (b 0 11) 12) H.
restrsublis H. 
(** subgoal 2 *)
 
simpl.
aply_blindness 3 8 12 0 1 (b 0 7) (b 1 11)  ((Mvar 0), (Mvar 1)) ((Mvar 0), (Mvar 1))  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                                                       msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); msg (sk 3) ] .
aplyprojn 1 16 H; try split; try reflexivity.
rep_commits 0 1 11 21 7 22 fr1 fr2 temp H H0.
rename H0 into H.
appconst H. 
x1checks x1 x1 H. 
funapp_vtrm 1 0 1 7 8 H.
x1checks (x2t 0 ) (x2t 1) H.
funapp_vtrm 2 1 0 11 12 H.
x1checks (x3tft 0 1) (x3tft 1 0) H.
adminchecks (x3tft 0 1) (x3tft 1 0) H.
 ver_suc 1 (pi1 (x3tft 0 1)) (e (b 0 7) 8) (pi1 (x3tft 1 0)) (e (b 1 7) 8) H.
ver_suc 2 (pi2 (x3tft 0 1)) (e (b 1 11) 12) (pi2 (x3tft 1 0)) (e (b 0 11) 12) H.

restrsublis H.
(** subgoal 3*)
simpl.
simpl.
aply_blindness 3 8 12 0 1 (b 0 7) (b 1 11)  ((Mvar 0), (Mvar 1)) ((Mvar 0), (Mvar 1))  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                                                       msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); msg (sk 3) ] .
aplyprojn 1 16 H; try split; try reflexivity.
rep_commits 0 1 11 21 7 22 fr1 fr2 temp H H0.
rename H0 into H.
appconst H. 
x1checks x1 x1 H. 
funapp_vtrm 1 0 1 7 8 H.
x1checks (x2t 0 ) (x2t 1) H.
funapp_vtrm 2 1 0 11 12 H.
x1checks (x3tft 0 1) (x3tft 1 0) H.
adminchecks (x3tft 0 1) (x3tft 1 0) H.
 ver_suc 1 (pi1 (x3tft 0 1)) (e (b 0 7) 8) (pi1 (x3tft 1 0)) (e (b 1 7) 8) H.
ver_suc 2 (pi2 (x3tft 0 1)) (e (b 1 11) 12) (pi2 (x3tft 1 0)) (e (b 0 11) 12) H.
restrsublis H.
(** subgola 4 *)
simpl.
aply_blindness 3 8 12 0 1 (b 0 7) (b 1 11)  ((Mvar 0), (Mvar 1)) ((Mvar 0), (Mvar 1))  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                                                       msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); msg (sk 3) ] .
aplyprojn 1 16 H; try split; try reflexivity.
rep_commits 0 1 11 21 7 22 fr1 fr2 temp H H0.
rename H0 into H.
appconst H. 
x1checks x1 x1 H. 
funapp_vtrm 1 0 1 7 8 H.
x1checks (x2t 0 ) (x2t 1) H.
funapp_vtrm 2 1 0 11 12 H.
x1checks (x3tft 0 1) (x3tft 1 0) H.
adminchecks (x3tft 0 1) (x3tft 1 0) H.
restrsublis H.
(** subgoal *)

simpl.
aply_blindness 3 8 12 0 1 (b 0 7) (b 1 7)  ((Mvar 0), (Mvar 1)) ((Mvar 0), (Mvar 1))  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                                                       msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); msg (sk 3) ] .
aplyprojn 2 15 H; try split; try reflexivity.
appconst H. 
x1checks x1 x1 H. 
funapp_vtrm 1 0 1 7 8 H.
x1checks (x2t 0 ) (x2t 1) H.
restrsublis H.
(** subgoal *)
simpl.
ufcma_pi1 (x3ftft 1 0).
ufcma_pi2 (x3ftft 1 0).
apply IFBRANCH_M3 with (ml1:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1))]) (ml2:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                             msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1))]).
simpl.
apply IFBRANCH_M2 with (ml1:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1)); 
    bol (eqm (to x1) (V 2));
    msg (pk 2, (e (b 1 9) 10, sign (sk 2) (e (b 1 9) 10)))]) (ml2:=  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1)); 
   bol (eqm (to x1) (V 2));
   msg (pk 2, (e (b 0 9) 10, sign (sk 2) (e (b 0 9) 10)))]).
simpl.
apply IFBRANCH_M1 with (ml1:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1)); 
    bol (eqm (to x1) (V 2));
    msg (pk 2, (e (b 1 9) 10, sign (sk 2) (e (b 1 9) 10)));
    bol (eqm (to (x2ft 1)) (V 1));
    msg (pk 1, (e (b 0 13) 14, sign (sk 1) (e (b 0 13) 14)))]) (ml2:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1)); 
   bol (eqm (to x1) (V 2));
   msg (pk 2, (e (b 0 9) 10, sign (sk 2) (e (b 0 9) 10)));
   bol (eqm (to (x2ft 0)) (V 1));
   msg (pk 1, (e (b 1 13) 14, sign (sk 1) (e (b 1 13) 14)))]).
simpl. 
apply IFBRANCH_M1 with (ml1:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1)); 
    bol (eqm (to x1) (V 2));
    msg (pk 2, (e (b 1 9) 10, sign (sk 2) (e (b 1 9) 10)));
    bol (eqm (to (x2ft 1)) (V 1));
    msg (pk 1, (e (b 0 13) 14, sign (sk 1) (e (b 0 13) 14)));
    bol (eqm (to (x3ftft 0 1)) (pk 3))]) (ml2:=  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1)); 
   bol (eqm (to x1) (V 2));
   msg (pk 2, (e (b 0 9) 10, sign (sk 2) (e (b 0 9) 10)));
   bol (eqm (to (x2ft 0)) (V 1));
   msg (pk 1, (e (b 1 13) 14, sign (sk 1) (e (b 1 13) 14)));
   bol (eqm (to (x3ftft 1 0)) (pk 3))]).
simpl.
apply IFBRANCH_M1 with (ml1:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1)); 
    bol (eqm (to x1) (V 2));
    msg (pk 2, (e (b 1 9) 10, sign (sk 2) (e (b 1 9) 10)));
    bol (eqm (to (x2ft 1)) (V 1));
    msg (pk 1, (e (b 0 13) 14, sign (sk 1) (e (b 0 13) 14)));
    bol (eqm (to (x3ftft 0 1)) (pk 3));
    bol
      (ifb (eqm (pi1 (pi2 (pi1 (x3ftft 0 1)))) (e (b 0 13) 14))
         (ver (pk 1) (e (b 0 13) 14) (pi2 (pi2 (pi1 (x3ftft 0 1))))) FAlse)]) (ml2:=  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
   msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1)); 
   bol (eqm (to x1) (V 2));
   msg (pk 2, (e (b 0 9) 10, sign (sk 2) (e (b 0 9) 10)));
   bol (eqm (to (x2ft 0)) (V 1));
   msg (pk 1, (e (b 1 13) 14, sign (sk 1) (e (b 1 13) 14)));
   bol (eqm (to (x3ftft 1 0)) (pk 3));
   bol
     (ifb (eqm (pi1 (pi2 (pi1 (x3ftft 1 0)))) (e (b 1 13) 14))
          (ver (pk 1) (e (b 1 13) 14) (pi2 (pi2 (pi1 (x3ftft 1 0))))) FAlse)]); try repeat
  (aply_blindness 3 10 14 0 1 (b 1 9) (b 0 13)  ((Mvar 0), (Mvar 1)) ((Mvar 0), (Mvar 1))  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                                                       msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); msg (sk 3) ] ; simpl;
aplyprojn 1 16 H; try split; try reflexivity;
rep_commits 1 0 13 21 9 22 fr1 fr2 temp H H0;
rename H0 into H;
appconst H;
x1checks x1 x1 H;
funapp_vtrm 2 1 0 9 10 H;
funapp_vtrm 1 0 1 13 14 H;
x1checks (x2ft 1 ) (x2ft 0) H;
x1checks (x3ftft 0 1) (x3ftft 1 0) H;
adminchecks (x3ftft 0 1) (x3ftft 1 0) H;
ver_suc 1 (pi1 (x3ftft 0 1)) (e (b 0 13) 14) (pi1 (x3ftft 1 0)) (e (b 1 13) 14) H;
ver_suc 2 (pi2 (x3ftft 0 1)) (e (b 1 9) 10) (pi2 (x3ftft 1 0)) (e (b 0 9) 10) H;
restrsublis H). 

(** subgoal *)
  (aply_blindness 3 10 14 0 1 (b 1 9) (b 0 13)  ((Mvar 0), (Mvar 1)) ((Mvar 0), (Mvar 1))  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                                                       msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); msg (sk 3) ] ; simpl;
aplyprojn 1 16 H; try split; try reflexivity;
rep_commits 1 0 13 21 9 22 fr1 fr2 temp H H0;
rename H0 into H;
appconst H;
x1checks x1 x1 H;
funapp_vtrm 2 1 0 9 10 H;
funapp_vtrm 1 0 1 13 14 H;
x1checks (x2ft 1 ) (x2ft 0) H;
x1checks (x3ftft 0 1) (x3ftft 1 0) H;
adminchecks (x3ftft 0 1) (x3ftft 1 0) H;
ver_suc 1 (pi1 (x3ftft 0 1)) (e (b 0 13) 14) (pi1 (x3ftft 1 0)) (e (b 1 13) 14) H;
ver_suc 2 (pi2 (x3ftft 0 1)) (e (b 1 9) 10) (pi2 (x3ftft 1 0)) (e (b 0 9) 10) H;
restrsublis H). try  (aply_blindness 3 10 14 0 1 (b 1 9) (b 0 13)  ((Mvar 0), (Mvar 1)) ((Mvar 0), (Mvar 1))  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                                                       msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); msg (sk 3) ] ; simpl;
aplyprojn 1 16 H; try split; try reflexivity;
rep_commits 1 0 13 21 9 22 fr1 fr2 temp H H0;
rename H0 into H;
appconst H;
x1checks x1 x1 H;
funapp_vtrm 2 1 0 9 10 H;
funapp_vtrm 1 0 1 13 14 H;
x1checks (x2ft 1 ) (x2ft 0) H;
x1checks (x3ftft 0 1) (x3ftft 1 0) H;
adminchecks (x3ftft 0 1) (x3ftft 1 0) H;
ver_suc 1 (pi1 (x3ftft 0 1)) (e (b 0 13) 14) (pi1 (x3ftft 1 0)) (e (b 1 13) 14) H;
ver_suc 2 (pi2 (x3ftft 0 1)) (e (b 1 9) 10) (pi2 (x3ftft 1 0)) (e (b 0 9) 10) H;
restrsublis H).

   (aply_blindness 3 10 14 0 1 (b 1 9) (b 0 13)  ((Mvar 0), (Mvar 1)) ((Mvar 0), (Mvar 1))  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                                                       msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); msg (sk 3) ] ; simpl;
aplyprojn 1 16 H; try split; try reflexivity;
rep_commits 1 0 13 21 9 22 fr1 fr2 temp H H0;
rename H0 into H;
appconst H;
x1checks x1 x1 H;
funapp_vtrm 2 1 0 9 10 H;
funapp_vtrm 1 0 1 13 14 H;
x1checks (x2ft 1 ) (x2ft 0) H;
x1checks (x3ftft 0 1) (x3ftft 1 0) H;
adminchecks (x3ftft 0 1) (x3ftft 1 0) H;
ver_suc 1 (pi1 (x3ftft 0 1)) (e (b 0 13) 14) (pi1 (x3ftft 1 0)) (e (b 1 13) 14) H;
ver_suc 2 (pi2 (x3ftft 0 1)) (e (b 1 9) 10) (pi2 (x3ftft 1 0)) (e (b 0 9) 10) H;
restrsublis H). reflexivity.
Qed. *)
End frame3.