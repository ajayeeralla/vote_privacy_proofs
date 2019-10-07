Load "foo_prot2".

   
(** Existential unforgeability under adaptively chosen message attacks (UF-CMA secure) *)

  Fixpoint bverufcma'  (j:nat) (n:nat)  (ml: list message) (t t' u :message) : Bool :=
    match j, ml with
      |  0 , _ => FAlse
      |  S _, nil  => FAlse             
      | S j', cons h tl => match h with
                             | (bsign ( pi2 (k (N n))) (blind t1 t2 t3)) =>   ifb  (eqm t t1)  & (eqm (pk n) t2) & (eqm t' t3) (bver (pk n) t (unblind t (pk n) t' u)) (bverufcma j' n tl t t'  u)
                             | _ => FAlse
                           end
    end.    

  Axiom SHU_UFCMA' : forall (n :nat)(t t' u: message), (clos_mylist [ msg t; msg t'; msg u] = true) /\ (insec_nbs_mylis n [msg t; msg t' ; msg u] = false) ->
                                               let j := length(list_skn_in_bsign n (app (subtrmls_msg t) (app (subtrmls_msg t') (subtrmls_msg u)))) in
                                               let ml := distbsigntrms n (app ( subtrmls_msg t) ( subtrmls_msg u)) in
                                               if (beq_nat j 0) then  ((bver (pk n) t (unblind t (pk n) t' u))  ## FAlse) else ((bver (pk n) t (unblind t (pk n) t' u))  ## (bverufcma j n ml t t' u)).
 
  (**************************************************************************************)
       
Ltac ufcma_pi1'  x :=
          repeat match goal with
            |[|- context[(ver (pk ?n') (pi1 (pi2 (pi1 x))) ?Y)] ] => rewrite UFCMA with (n:= n') (t:= (pi1 (pi2 (pi1 x)))) (u:= Y)   ;  simpl ; repeat (try rewrite IFSAME_B; try rewrite IFFALSE_B; try rewrite IFFALSE_M); try split; try reflexivity
          end. 
  
      Ltac ufcma_pi2' x:=  
              repeat match goal with
                       |[|- context[(ver (pk ?n1) (pi1 (pi2 (pi2 x))) ?Y)] ] => rewrite UFCMA with (n:=n1) (t:= (pi1 (pi2 (pi2 x)))) (u:= Y)  ; simpl ; repeat (try rewrite IFSAME_B; try rewrite IFFALSE_B; try rewrite IFFALSE_M); try split; try reflexivity
                     end.                                                                                                                                                             Ltac unforge' x1 n1 n2:= 
                         ufcma_pi1' (x1 n1 n2); ufcma_pi2' (x1 n1 n2);   ufcma_pi1' (x1 n2 n1);   ufcma_pi2' (x1 n2 n1).
                       
Ltac aply_andB_elm' B2 := 
match goal with 
|[|- context[ifm (ifb ?B1 B2 FAlse) ?T1 ?T2 ] ] => rewrite andB_elm' with (b1:= B1) (b2:= B2) (x:= T1) (y:= T2)
end.
 Ltac aply_bver' := 
  match goal with
    |[|- context[bver (pk ?N) ?T  (unblind ?T (pk ?N) ?T' ?U) ] ] => rewrite SHU_UFCMA with (n:= N) (t:=T) (t':= T') (u:= U) 
  end.
 Ltac btrm n x1 b1 x2 b2  H :=  
  funapptrmhyp (bol (ifb (eqm (pi1 (pi2 x1)) b1)
            (ver (pk n) b1 (pi2 (pi2 x1))) FAlse)) (bol (ifb (eqm (pi1 (pi2 x2)) b2) (ver (pk n) b2 (pi2 (pi2 x2))) FAlse)) H.
Theorem frame5ind : (phi5 0 1) ~ (phi5 1 0).
Proof. unfold phi5, phi4, phi3, phi2, phi1, phi0. unfold t1, t2, t3, t4.
       simpl. repeat unf. repeat unfold admin, achecks.
       
      
       repeat unfold q1_s, q1_ss, q1_sss, q2_s, q2_ss, q2_sss.  repeat unfold q11, q12, q13, q21, q22, q23, q11_s, q12_s, q13_s, q21_s, q22_s, q23_s.
       repeat unfold  q11_ss, q12_ss, q13_ss, q21_ss, q22_ss, q23_ss.
       repeat unfold q111, q112, q121, q122, q123, q121, q132, q211, q212, q221, q222, q223, q231, q232, q311, q312, q321, q322; repeat unfold q111_s, q112_s, q121_s, q122_s, q123_s, q121_s, q132_s, q211_s, q212_s, q221_s, q222_s, q223_s, q231_s, q232_s, q311_s, q312_s, q321_s, q322_s.  repeat unfold andB; repeat unfold admin, achecks.
      (*  pose proof(UFCMA).
       rewrite UFCMA with (n:= 1) (t:=(pi1 (pi2( pi1 x1)))) (u:= (pi2 (pi2 (pi1 x1)))). simpl. *) 
   
                      
      ufcma_pi1' x1;
       ufcma_pi1' (x2t 0);
       ufcma_pi1' (x2t 1); 
       ufcma_pi2' (x2t 0);  ufcma_pi2' (x2t 1);
       ufcma_pi1' (x2ft 1); ufcma_pi1' (x2ft 0); 
       ufcma_pi1' (x3tt 0); ufcma_pi1' (x3tt 1);
       ufcma_pi2' (x3tt 0); ufcma_pi2' (x3tt 1);
       ufcma_pi1' (x3ftt 1); ufcma_pi1' (x3ftt 0).
        
        unforge' x3tft 0 1;
       unforge' x3ftft 0 1;
       unforge' x4tftt 0 1;
       unforge' x4fttt 0 1;
       unforge' x4ftftt 0 1.
       
        
      
  
 

repeat aply_andB_elm'  (bacc (pk 3) (b 0 7) (r 8) (pi1 (x2t 0))). 
repeat aply_andB_elm'  (bacc (pk 3) (b 1 7) (r 8) (pi1 (x2t 1))).
   
 
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.   
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.
repeat redg.
repeat aply_andB_elm' (bacc (pk 3) (b 1 9) (r 10) (pi2 (x2ft 1))); repeat aply_andB_elm' (bacc (pk 3) (b 0 9) (r 10) (pi2 (x2ft 0))).
rew_mupbver; aply_bver'; simpl; try split ; try reflexivity. 
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
rew_mupbver; aply_bver'; simpl;  repeat rewrite -> IFFALSE_M.
rew_mupbver; aply_bver'; simpl;  repeat rewrite -> IFFALSE_M.
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
repeat redg. 
repeat unfold andB.
repeat aply_andB_elm' (bacc (pk 3) (b 0 7) (r 8) (pi2 (x3tft 0 1))  ).
repeat aply_andB_elm' (bacc (pk 3) (b 1 7) (r 8) (pi2 (x3tft 1 0))).
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M. 
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M. 
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M. 
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M. 
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
repeat redg.
repeat aply_andB_elm' (bacc (pk 3) (b 1 11) (r 12) (pi2 (x3tft 0 1))); repeat aply_andB_elm' (bacc (pk 3) (b 0 11) (r 12) (pi2 (x3tft 1 0))).
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
repeat redg.

repeat aply_andB_elm' (bacc (pk 3) (b 0 13) (r 14) (pi1 (x3ftft 0 1))); repeat aply_andB_elm' (bacc (pk 3) (b 1 13) (r 14) (pi1 (x3ftft 1 0))).

rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
repeat redg.
repeat aply_andB_elm' (bacc (pk 3) (b 1 9) (r 10) (pi2 (x3ftft 0 1))); repeat aply_andB_elm' (bacc (pk 3) (b 0 9) (r 10) (pi2 (x3ftft 1 0))).
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  

(** x4 *)

repeat aply_andB_elm' (bacc (pk 3) (b 0 7) (r 8) (pi1 (x4tftfft 0 1))); repeat aply_andB_elm' (bacc (pk 3) (b 1 7) (r 8) (pi1 (x4tftfft 1 0))).
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
repeat redg.
repeat aply_andB_elm' (bacc (pk 3) (b 1 11) (r 12) (pi2 (x4tftfft 0 1))); repeat aply_andB_elm' (bacc (pk 3) (b 0 11) (r 12) (pi2 (x4tftfft 1 0))).
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
repeat redg.

repeat aply_andB_elm' (bacc (pk 3) (b 0 13) (r 14) (pi1 (x4ftftfft 0 1))); repeat aply_andB_elm' (bacc (pk 3) (b 1 13) (r 14) (pi1 (x4ftftfft 1 0))).
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
repeat redg. 

(** all bacc eleminated *)

 apply IFBRANCH_M5 with (ml1:= phi0) (ml2:= phi0).
 simpl.
 aply_blindness 3 8 12 0 1 (b 0 7) (b 1 11)  ((Mvar 0), (Mvar 1)) ((Mvar 0), (Mvar 1))  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                                                       msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); msg (sk 3) ] ; simpl;
aplyprojn 1 16 H; try split; try reflexivity.
rep_commits 0 1 11 30 7 31 fr1 fr2 temp H H0.
rename H0 into H;
appconst H;
x1checks x1 x1 H;
funapp_vtrm 1 0 1 7 8 H;
funapp_vtrm 2 1 0 11 12 H.
x1checks (x2t 0) (x2t 1) H.
x1checks (x3tft 0 1) (x3tft 1 0) H. 
adminchecks (x3tft 0 1) (x3tft 1 0) H.
funapptrmhyp  (msg
      (ifm (eqm (to (x2t 0)) (V 2))
         (pk 2, (e (b 1 11) 12, sign (sk 2) (e (b 1 11) 12))) O)) (msg
      (ifm (eqm (to (x2t 1)) (V 2))
           (pk 2, (e (b 0 11) 12, sign (sk 2) (e (b 0 11) 12))) O)) H.



ver_suc1 2 (pi2 (x3tft 0 1)) (e (b 1 11) 12) (pi2 (x3tft 1 0)) (e (b 0 11) 12) H.



btrm 2 (pi2 (x3tft 0 1))   (e (b 1 11) 12) (pi2 (x3tft 1 0)) (e (b 0 11) 12) H.
 
 
ver_suc1 1 (pi1 (x3tft 0 1)) (e (b 0 7) 8) (pi1 (x3tft 1 0)) (e (b 1 7) 8) H.
 btrm 1 (pi1 (x3tft 0 1)) (e (b 0 7) 8) (pi1 (x3tft 1 0)) (e (b 1 7) 8) H. 
  

funapptrmhyp   (bol (ifb (eqm (to (x3tft 0 1)) (pk 3))
           (ifb (eqm (pi1 (pi2 (pi1 (x3tft 0 1)))) (e (b 0 7) 8))
              (ver (pk 1) (e (b 0 7) 8) (pi2 (pi2 (pi1 (x3tft 0 1))))) FAlse)
           FAlse)) (bol (ifb (eqm (to (x3tft 1 0)) (pk 3))
           (ifb (eqm (pi1 (pi2 (pi1 (x3tft 1 0)))) (e (b 1 7) 8))
              (ver (pk 1) (e (b 1 7) 8) (pi2 (pi2 (pi1 (x3tft 1 0))))) FAlse)
           FAlse))  H.
funapptrmhyp (bol (ifb
         (ifb (eqm (to (x3tft 0 1)) (pk 3))
            (ifb (eqm (pi1 (pi2 (pi1 (x3tft 0 1)))) (e (b 0 7) 8))
               (ver (pk 1) (e (b 0 7) 8) (pi2 (pi2 (pi1 (x3tft 0 1))))) FAlse)
            FAlse)
         (ifb (eqm (pi1 (pi2 (pi2 (x3tft 0 1)))) (e (b 1 11) 12))
            (ver (pk 2) (e (b 1 11) 12) (pi2 (pi2 (pi2 (x3tft 0 1))))) FAlse)
         FAlse)) (bol (ifb
         (ifb (eqm (to (x3tft 1 0)) (pk 3))
            (ifb (eqm (pi1 (pi2 (pi1 (x3tft 1 0)))) (e (b 1 7) 8))
               (ver (pk 1) (e (b 1 7) 8) (pi2 (pi2 (pi1 (x3tft 1 0))))) FAlse)
            FAlse)
         (ifb (eqm (pi1 (pi2 (pi2 (x3tft 1 0)))) (e (b 0 11) 12))
            (ver (pk 2) (e (b 0 11) 12) (pi2 (pi2 (pi2 (x3tft 1 0))))) FAlse)
         FAlse)) H.
funapptrmhyp (msg (ifm
            (ifb
               (ifb (eqm (to (x3tft 0 1)) (pk 3))
                  (ifb (eqm (pi1 (pi2 (pi1 (x3tft 0 1)))) (e (b 0 7) 8))
                     (ver (pk 1) (e (b 0 7) 8) (pi2 (pi2 (pi1 (x3tft 0 1)))))
                     FAlse) FAlse)
               (ifb (eqm (pi1 (pi2 (pi2 (x3tft 0 1)))) (e (b 1 11) 12))
                  (ver (pk 2) (e (b 1 11) 12) (pi2 (pi2 (pi2 (x3tft 0 1)))))
                  FAlse) FAlse)
            (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 0 1)))),
            bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 0 1))))) O)) (msg (ifm
           (ifb
              (ifb (eqm (to (x3tft 1 0)) (pk 3))
                 (ifb (eqm (pi1 (pi2 (pi1 (x3tft 1 0)))) (e (b 1 7) 8))
                    (ver (pk 1) (e (b 1 7) 8) (pi2 (pi2 (pi1 (x3tft 1 0)))))
                    FAlse) FAlse)
              (ifb (eqm (pi1 (pi2 (pi2 (x3tft 1 0)))) (e (b 0 11) 12))
                 (ver (pk 2) (e (b 0 11) 12) (pi2 (pi2 (pi2 (x3tft 1 0)))))
                 FAlse) FAlse)
           (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 1 0)))),
           bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 1 0))))) O)) H.
funapptrmhyp (  msg
      (ifm (eqm (to (x2t 0)) (V 2))
         (ifm
            (ifb
               (ifb (eqm (to (x3tft 0 1)) (pk 3))
                  (ifb (eqm (pi1 (pi2 (pi1 (x3tft 0 1)))) (e (b 0 7) 8))
                     (ver (pk 1) (e (b 0 7) 8) (pi2 (pi2 (pi1 (x3tft 0 1)))))
                     FAlse) FAlse)
               (ifb (eqm (pi1 (pi2 (pi2 (x3tft 0 1)))) (e (b 1 11) 12))
                  (ver (pk 2) (e (b 1 11) 12) (pi2 (pi2 (pi2 (x3tft 0 1)))))
                  FAlse) FAlse)
            (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 0 1)))),
            bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 0 1))))) O) O)) (msg
     (ifm (eqm (to (x2t 1)) (V 2))
        (ifm
           (ifb
              (ifb (eqm (to (x3tft 1 0)) (pk 3))
                 (ifb (eqm (pi1 (pi2 (pi1 (x3tft 1 0)))) (e (b 1 7) 8))
                    (ver (pk 1) (e (b 1 7) 8) (pi2 (pi2 (pi1 (x3tft 1 0)))))
                    FAlse) FAlse)
              (ifb (eqm (pi1 (pi2 (pi2 (x3tft 1 0)))) (e (b 0 11) 12))
                 (ver (pk 2) (e (b 0 11) 12) (pi2 (pi2 (pi2 (x3tft 1 0)))))
                 FAlse) FAlse)
           (bsign (sk 3) (pi1 (pi2 (pi1 (x3tft 1 0)))),
           bsign (sk 3) (pi1 (pi2 (pi2 (x3tft 1 0))))) O) O)) H.
restrsublis H.
(** subgoal *)
simpl.
repeat redg.
repeat unfold q2232.
apply IFBRANCH_M5 with (ml1:= [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
    msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1))]) (ml2:=   [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                               msg (N 4); msg (pk 5); bol (eqm (to x1) (V 1))]). simpl.
(** subgoal *)
 repeat aply_andB_elm' (bacc (pk 3) (b 1 9) (r 10) (pi2 (x4ftftfft 0 1))). repeat aply_andB_elm' (bacc (pk 3) (b 0 9) (r 10) (pi2 (x4ftftfft 1 0))). 
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.  
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.    
rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.

repeat redg.

rew_mupbver; aply_bver'; simpl; repeat rewrite -> IFFALSE_M.
repeat redg.
aply_blindness 3 10 14 0 1 (b 1 9) (b 0 13)  ((Mvar 0), (Mvar 1)) ((Mvar 0), (Mvar 1))  [msg (pk 0); msg (pk 1); msg (pk 2); msg (pk 3); 
                                                                                       msg (N 4); msg (pk 5); msg (sk 1); msg (sk 2); msg (sk 3) ] ; simpl;
aplyprojn 1 16 H; try split; try reflexivity.
rep_commits 1 0 13 30 9 31 fr1 fr2 temp H H0.
rename H0 into H;
appconst H;
x1checks x1 x1 H;
funapp_vtrm 2 1 0 9 10 H;
funapp_vtrm 1 0 1 13 14 H.
x1checks (x2ft 1) (x2ft 0) H.
x1checks (x3ftft 0 1) (x3ftft 1 0) H. 
adminchecks (x3ftft 0 1) (x3ftft 1 0) H.
funapptrmhyp (msg
      (ifm (eqm (to (x2ft 1)) (V 1))
         (pk 1, (e (b 0 13) 14, sign (sk 1) (e (b 0 13) 14))) O))  (msg
     (ifm (eqm (to (x2ft 0)) (V 1))
        (pk 1, (e (b 1 13) 14, sign (sk 1) (e (b 1 13) 14))) O)) H.

 

ver_suc1 2 (pi2 (x3ftft 0 1)) (e (b 1 9) 10) (pi2 (x3ftft 1 0)) (e (b 0 9) 10) H.



btrm 2 (pi2 (x3ftft 0 1))   (e (b 1 9) 10) (pi2 (x3ftft 1 0)) (e (b 0 9) 10) H.
 
 
ver_suc1 1 (pi1 (x3ftft 0 1)) (e (b 0 13) 14) (pi1 (x3ftft 1 0)) (e (b 1 13) 14) H.
 btrm 1 (pi1 (x3ftft 0 1)) (e (b 0 13) 14) (pi1 (x3ftft 1 0)) (e (b 1 13) 14) H. 
  

funapptrmhyp (bol (ifb (eqm (pi1 (pi2 (pi1 (x3ftft 0 1)))) (e (b 0 13) 14))
                     (ver (pk 1) (e (b 0 13) 14)
                        (pi2 (pi2 (pi1 (x3ftft 0 1))))) FAlse)) (bol   (ifb (eqm (pi1 (pi2 (pi1 (x3ftft 1 0)))) (e (b 1 13) 14))
                    (ver (pk 1) (e (b 1 13) 14)
                         (pi2 (pi2 (pi1 (x3ftft 1 0))))) FAlse)) H. 
funapptrmhyp (bol (ifb (eqm (to (x3ftft 0 1)) (pk 3))
                  (ifb (eqm (pi1 (pi2 (pi1 (x3ftft 0 1)))) (e (b 0 13) 14))
                     (ver (pk 1) (e (b 0 13) 14)
                        (pi2 (pi2 (pi1 (x3ftft 0 1))))) FAlse) FAlse)) (bol   (ifb (eqm (to (x3ftft 1 0)) (pk 3))
                 (ifb (eqm (pi1 (pi2 (pi1 (x3ftft 1 0)))) (e (b 1 13) 14))
                    (ver (pk 1) (e (b 1 13) 14)
                         (pi2 (pi2 (pi1 (x3ftft 1 0))))) FAlse) FAlse)) H.
funapptrmhyp (bol 
            (ifb
               (ifb (eqm (to (x3ftft 0 1)) (pk 3))
                  (ifb (eqm (pi1 (pi2 (pi1 (x3ftft 0 1)))) (e (b 0 13) 14))
                     (ver (pk 1) (e (b 0 13) 14)
                        (pi2 (pi2 (pi1 (x3ftft 0 1))))) FAlse) FAlse)
               (ifb (eqm (pi1 (pi2 (pi2 (x3ftft 0 1)))) (e (b 1 9) 10))
                  (ver (pk 2) (e (b 1 9) 10) (pi2 (pi2 (pi2 (x3ftft 0 1)))))
                  FAlse) FAlse))
          (bol  
           (ifb
              (ifb (eqm (to (x3ftft 1 0)) (pk 3))
                 (ifb (eqm (pi1 (pi2 (pi1 (x3ftft 1 0)))) (e (b 1 13) 14))
                    (ver (pk 1) (e (b 1 13) 14)
                       (pi2 (pi2 (pi1 (x3ftft 1 0))))) FAlse) FAlse)
              (ifb (eqm (pi1 (pi2 (pi2 (x3ftft 1 0)))) (e (b 0 9) 10))
                 (ver (pk 2) (e (b 0 9) 10) (pi2 (pi2 (pi2 (x3ftft 1 0)))))
                 FAlse) FAlse)) H.

funapptrmhyp (msg (ifm
            (ifb
               (ifb (eqm (to (x3ftft 0 1)) (pk 3))
                  (ifb (eqm (pi1 (pi2 (pi1 (x3ftft 0 1)))) (e (b 0 13) 14))
                     (ver (pk 1) (e (b 0 13) 14)
                        (pi2 (pi2 (pi1 (x3ftft 0 1))))) FAlse) FAlse)
               (ifb (eqm (pi1 (pi2 (pi2 (x3ftft 0 1)))) (e (b 1 9) 10))
                  (ver (pk 2) (e (b 1 9) 10) (pi2 (pi2 (pi2 (x3ftft 0 1)))))
                  FAlse) FAlse)
            (bsign (sk 3) (pi1 (pi2 (pi1 (x3ftft 0 1)))),
            bsign (sk 3) (pi1 (pi2 (pi2 (x3ftft 0 1))))) O))   (msg (ifm
           (ifb
              (ifb (eqm (to (x3ftft 1 0)) (pk 3))
                 (ifb (eqm (pi1 (pi2 (pi1 (x3ftft 1 0)))) (e (b 1 13) 14))
                    (ver (pk 1) (e (b 1 13) 14)
                       (pi2 (pi2 (pi1 (x3ftft 1 0))))) FAlse) FAlse)
              (ifb (eqm (pi1 (pi2 (pi2 (x3ftft 1 0)))) (e (b 0 9) 10))
                 (ver (pk 2) (e (b 0 9) 10) (pi2 (pi2 (pi2 (x3ftft 1 0)))))
                 FAlse) FAlse)
           (bsign (sk 3) (pi1 (pi2 (pi1 (x3ftft 1 0)))),
           bsign (sk 3) (pi1 (pi2 (pi2 (x3ftft 1 0))))) O)) H.

  funapptrmhyp ( msg
      (ifm (eqm (to (x2ft 1)) (V 1))
         (ifm
            (ifb
               (ifb (eqm (to (x3ftft 0 1)) (pk 3))
                  (ifb (eqm (pi1 (pi2 (pi1 (x3ftft 0 1)))) (e (b 0 13) 14))
                     (ver (pk 1) (e (b 0 13) 14)
                        (pi2 (pi2 (pi1 (x3ftft 0 1))))) FAlse) FAlse)
               (ifb (eqm (pi1 (pi2 (pi2 (x3ftft 0 1)))) (e (b 1 9) 10))
                  (ver (pk 2) (e (b 1 9) 10) (pi2 (pi2 (pi2 (x3ftft 0 1)))))
                  FAlse) FAlse)
            (bsign (sk 3) (pi1 (pi2 (pi1 (x3ftft 0 1)))),
            bsign (sk 3) (pi1 (pi2 (pi2 (x3ftft 0 1))))) O) O))   (msg
     (ifm (eqm (to (x2ft 0)) (V 1))
        (ifm
           (ifb
              (ifb (eqm (to (x3ftft 1 0)) (pk 3))
                 (ifb (eqm (pi1 (pi2 (pi1 (x3ftft 1 0)))) (e (b 1 13) 14))
                    (ver (pk 1) (e (b 1 13) 14)
                       (pi2 (pi2 (pi1 (x3ftft 1 0))))) FAlse) FAlse)
              (ifb (eqm (pi1 (pi2 (pi2 (x3ftft 1 0)))) (e (b 0 9) 10))
                 (ver (pk 2) (e (b 0 9) 10) (pi2 (pi2 (pi2 (x3ftft 1 0)))))
                 FAlse) FAlse)
           (bsign (sk 3) (pi1 (pi2 (pi1 (x3ftft 1 0)))),
            bsign (sk 3) (pi1 (pi2 (pi2 (x3ftft 1 0))))) O) O)) H.
  restrsublis H.
  Focus 6. reflexivity.
  repeat (try split; try reflexivity).
 do 50 (split; reflexivity). 
  split; reflexivity.
  split; reflexivity. split; reflexivity. split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
  split; reflexivity.
   split; reflexivity. Qed.