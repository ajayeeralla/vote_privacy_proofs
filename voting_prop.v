 
(************************************************************************)
(* Copyright (c) 2017-2018, Ajay Kumar Eeralla <ae266@mail.missouri.edu>*)     
(************************************************************************)
     
Require Export cpacca.
SearchAbout pair.
 
Axiom gen_ifmf_f3: forall (b:Bool) (t1 t2 t3 t4: message) {f}, (f (If b then t1 else t2) t3 t4) # If b then (f t1 t3 t4) else (f t2 t3 t4).

Axiom len_reg: forall x1 y1 x2 y2, (|x1|#?|y1|) & (|x2|#?|y2|) ## TRue ->  (|(x1, x2)| #? |(y1, y2)|) ## TRue. 
Axiom Example14_M: forall (m1 m2: message), (eqm m1 m2) ##  (eqm m2 m1).



Axiom clos_sub_vtrm: forall n1 s1 n2 s2 t, let mvl:= (distMvars [msg t]) in [n1;n2]= mvl \/ [n2;n1] = mvl -> closMsg ({{n1:=s1}} ({{n2:=s2}}t)) = true. 


Axiom cca2comp_sym : forall t1 t2 n1 n2 t3 t4 t, (cca2compmsg t1 t2 n1 n2 t3 t4 t) = (cca2compmsg t1 t2 n1 n2 t4 t3 t).
Axiom gen_ifmf_eql1: forall b t1 t2 t3 t4 t5 t6 t7 t8 t9 t10,  (If b then ((If (|(t1, t2)|) #? (|(t3,t4)|) then t5 else t6, t7), (t8, t9)) else t10) #  (If b then ((If (|(t1, (If b then t2 else O))|) #? (|(t3, (If b then t4 else O))|) then t5 else t6, t7), (t8, t9)) else t10).
Axiom gen_ifmf_eql2: forall b t1 t2 t3 t4, (|If b then t1 else t2| #? |If b then t3 else t4|)  ## (IF b then (|t1|#?|t3|) else (|t2|#?|t4|)).
Axiom gen_ifmf_eql3: forall b t1 t2 t3 t4 t5 t6 t7 t8 t9 t10,  (If b then ((t8, t7), (If (|(t1, t2)|) #? (|(t3,t4)|) then t5 else t6, t9)) else t10) #  (If b then ((t8, t7), (If (|(t1, (If b then t2 else O))|) #? (|(t3, (If b then t4 else O))|) then t5 else t6, t9)) else t10).

Theorem votingProp:  forall (t t0 t1 : message),   let v0 := (V0 (N 0)) in
                                                   let v1 := (V1 (N 0)) in
                                                                                                      (|v0|#?|v1|) ## TRue ->  (Fresh [1; 2; 3; 4] ([msg t, msg v0, msg v1, msg t0, msg t1])  = true) ->  closMylist ([msg t]) = true -> ((length (distMvars [msg t0, msg t1]))=?  2)%nat = true -> bVarMylist [msg t0, msg t1] = nil  ->
    let mvl:= [5; 6] in  (mVarMsg t0) = mvl /\ (mVarMsg t1) = mvl ->
                 let r0 := (r 1) in
                 let r1 := (r 2) in
                 let k0 := (kc (N 3)) in
                 let k1 := (kc (N 4)) in
                 let c00 := (comm v0 k0) in
                 let c01 := (comm v0 k1) in
                 let c10 := (comm v1 k0) in
                 let c11 := (comm v1 k1) in
                 let t2 := ({{ 5 := (bl c00 t r0) }} ({{ 6:=(bl c11 t r1) }} t0)) in
                 let t3 := ({{ 5 := (bl c00 t r0) }} ({{ 6:=(bl c11 t r1) }} t1)) in
                 let t4 := ({{ 5 := (bl c10 t r0) }} ({{ 6:=(bl c01 t r1) }} t0)) in
                 let t5 := ({{ 5 := (bl c10 t r0) }} ({{ 6:=(bl c01 t r1) }} t1)) in
                 let e00 := (enc (c00, (ub c00 t r0 t2)) (pke 11) (er 7)) in
                 let e11 := (enc (c11, (ub c11 t r1 t3)) (pke 11) (er 8)) in
                 let e10 := (enc (c10, (ub c10 t r0 t4)) (pke 11) (er 7)) in
                 let e01 := (enc (c01, (ub c01 t r1 t5)) (pke 11) (er 8)) in 
                 let ek0 := (enc k0 (pke 11) (er 9)) in
                 let ek1 := (enc k1 (pke 11) (er 10)) in
                 let lt1 := ((e00, ek0), (e11, ek1)) in
                 let lt2 := (e00, |_) in
                 let lt3 := (|_, e11) in
                 let rt1 := ((e10, ek0), (e01, ek1)) in
                 let rt2 := (|_, e01) in
                 let rt3 := (e10, |_) in
                 (cca2compmylis O O 0 11 k0 k1 [msg t, msg t0, msg t1] = true) -> (cca2compmylis O O 0 11 (c01, ub c01 t r1 t5) (c10, ub c10 t r0 t4) [msg t, msg t0, msg t1] = true) ->
                 (occur_name_mylist 100 [msg t, msg t0, msg t1] = false) ->
                 ([msg (bl c00 t r0), msg (bl c11 t r1),
                        msg (If (acc c00 t r0 t2)& (acc c11 t r1 t3) then lt1 else (If (acc c00 t r0 t2) then lt2 else (If (acc c11 t r1 t3) then lt3  else (|_, |_))))])
                    ~
                   
                    ([msg (bl c10 t r0), msg (bl c01 t r1),
                      msg (If (acc c10 t r0 t4)& (acc c01 t r1 t5) then rt1 else (If (acc c01 t r1 t5)  then rt2 else (If (acc c10 t r0 t4) then rt3 else (|_, |_))))]).

Proof. 
      intros  t t0 t1 v0 v1 H H0 H1 H2 H3 mvl H4 r0 r1 k0 k1 c00 c01 c10 c11 t2 t3 t4 t5 e00 e11 e10 e01 ek0 ek1 lt1 lt2 lt3 rt1 rt2 rt3 H5 H6 nd.
       assert( {{5 := bl c10 t r0}} ({{6 := bl c01 t r1}} (t0)) # t4); try reflexivity.
       assert( {{5 := bl c10 t r0}} ({{6 := bl c01 t r1}} (t1)) # t5); try reflexivity.
       pose proof(ext_blind_gen t t0 t1 [ msg c00, msg c11, msg k0, msg k1, msg (pke 11), msg (er 7), msg (er 8), msg (er 9), msg (er 10)]).
unfold lt1, rt1 in H9. simpl in H9.
funappf1 pi1 13 H9;auto.

funappf1 pi2 14 H9.
repeat rewrite gen_ifmf_f1 in H9.
repeat rewrite proj1, proj2 in H9. 
funappf1 pi1 1 H9. 
funappf1 pi2 2 H9.
funappf1 pi1 1 H9.
funappf1 pi2 2 H9.

funappf1 pi1 6 H9.
funappf1 pi2 7 H9.
funappf1 pi1 1 H9.
funappf1 pi2 2 H9.

repeat rewrite gen_ifmf_f1 in H9.
repeat rewrite proj1, proj2 in H9.
 
funappf3m enc 1 15 18 H9.
funappf3m enc 6 16 20 H9.
funappf2m pair 4 6 H9. 
repeat rewrite gen_ifmf_f2' in H9.
funappf2m pair 9 11 H9.
repeat rewrite gen_ifmf_f2' in H9.
funappf3m enc 2 19 20 H9.
funappf3m enc 2 20 22 H9.

repeat rewrite gen_ifmf_f3 in H9. 
funappf2m pair 1 5 H9.

funappf2m pair 3 7 H9.
repeat rewrite gen_ifmf_f2' in H9. simpl.
funappf2m pair 1 2 H9.
repeat rewrite gen_ifmf_f2' in H9.

(** swap inner else branches rt2 and rt3 on the right side *)
rewrite swapElseBranches with (t1:= rt3).
 
       rewrite DupBoolCond with (b:= (acc c00 t r0 t2) & (acc c11 t r1 t3)) (t1:= lt1) (t3:= let p:= |_ in let p1:=(pi1 (pi2 p), pi1 p) in let p2:= pi2 (pi2 p) in  ({p1 }_ 11 ^^ 7, {p2}_ 11 ^^ 9,
                    ({ p1 }_ 11 ^^ 8, {p2 }_ 11 ^^ 10))).
        rewrite DupBoolCond with (b:= (acc c10 t r0 t4) & (acc c01 t r1 t5)) (t1:= rt1) (t3:= let p:= |_ in let p1:=(pi1 (pi2 p), pi1 p) in let p2:= pi2 (pi2 p) in  ({p1 }_ 11 ^^ 7, {p2}_ 11 ^^ 9,
                    ({ p1 }_ 11 ^^ 8, {p2 }_ 11 ^^ 10))). simpl.
        apply IFBRANCH_M1 with (ml1:= [msg (bl c00 t r0), msg (bl c11 t r1)]) (ml2:= [msg (bl c10 t r0), msg (bl c01 t r1)]). simpl.
        unfold lt1, rt1.
unfold e10, e01. 

assert(let ct:= (comm (V0 (N 0)) (kc (N 4)),
                     ub (comm (V0 (N 0)) (kc (N 4))) t r1 t5) in 
                         
       let ct':= (comm (V1 (N 0)) (kc (N 3)),
                     ub (comm (V1 (N 0)) (kc (N 3))) t r0 t4) in
                       
       let p:= |_ in let p1:=(pi1 (pi2 p), pi1 p) in let p2:= pi2 (pi2 p) in   [msg (bl c00 t r0), msg (bl c11 t r1), bol (acc c00 t r0 t2) & (acc c11 t r1 t3),
   msg
     (If (acc c00 t r0 t2) & (acc c11 t r1 t3)
         then (e00, ek0, (e11, ek1)) 
         else ({p1 }_ 11 ^^ 7, {p2}_ 11 ^^ 9, ({ p1 }_ 11 ^^ 8, {p2 }_ 11 ^^ 10)))] ~
  [msg (bl c10 t r0), msg (bl c01 t r1), bol (acc c10 t r0 t4) & (acc c01 t r1 t5),
  msg
    (If (acc c10 t r0 t4) & (acc c01 t r1 t5)
        then ({ct }_ 11 ^^ 7,
                   {kc (N 4) }_ 11 ^^ 9,
                   ({ct'}_ 11 ^^ 8,
                   {kc (N 3) }_ 11 ^^ 10)) 
        else ({p1 }_ 11 ^^ 7, {p2}_ 11 ^^ 9, ({ p1 }_ 11 ^^ 8, {p2 }_ 11 ^^ 10)))]).
simpl. 
   restrsublis H9.
Focus 2. 
simpl.
repeat rewrite msg_beq_refl; auto. simpl.
Focus 2. 
simpl. repeat rewrite msg_beq_refl; auto. simpl. apply H9. clear H9.

(** Apply ENCCA2:1 **)


pose proof (let ct:= (comm (V0 (N 0)) (kc (N 4)),
                     ub (comm (V0 (N 0)) (kc (N 4))) t r1 t5) in
                      
       let ct':= (comm (V1 (N 0)) (kc (N 3)),
                     ub (comm (V1 (N 0)) (kc (N 3))) t r0 t4) in 
                    
       let p:= |_ in let p1:=(pi1 (pi2 p), pi1 p) in let p2:= pi2 (pi2 p) in ENCCCA2 O O ct ct' O 0 11 7 7 [msg (bl c10 t r0), msg (bl c01 t r1), bol (acc c10 t r0 t4) & (acc c01 t r1 t5),
  msg
    (If (acc c10 t r0 t4) & (acc c01 t r1 t5)
        then (Mvar 0,
                   {kc (N 4) }_ 11 ^^ 9,
                   ({ct'}_ 11 ^^ 8,
                   {kc (N 3) }_ 11 ^^ 10)) 
     else ({p1 }_ 11 ^^ 7, {p2}_ 11 ^^ 9, ({ p1 }_ 11 ^^ 8, {p2 }_ 11 ^^ 10)))]).

simpl in H9. 

 


(*repeat rewrite len_reg in H9. simpl in H1. *)
  
rewrite sub_clos with (t:=t) in H9; simpl in H1; try rewrite Bool.andb_true_r in H1; auto.
rewrite sub_clos with (t:=t) in H9; simpl in H1; try rewrite Bool.andb_true_r in H1; auto.

assert( (| comm (V0 (N 0)) (kc (N 4)) |) #? (| comm (V1 (N 0)) (kc (N 3)) |) ## TRue).
pose proof(commEql 4 3 v0 v1). 


rewrite H in H11; try rewrite IFTRUE_B in H11. 
apply H11; try split; try unfold Fresh; auto.

repeat rewrite H11 in H9.
repeat rewrite andB_TRue_l in H9.
simpl.
 
 simpl in H9.
 rewrite sub_ident with (n:=0) (t:= t4) in H9.
 rewrite sub_ident with (n:=0) (t:= t4) in H9.
 rewrite sub_ident with (n:=0) (t:= t5) in H9.
 rewrite sub_ident with (n:=0) (t:= t5) in H9. simpl in H9. simpl.
 
 fold (acc (comm (V1 (N 0)) (kc (N 3))) t (rb (N 1)) t4) & (acc (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2)) t5) in H9. 

 
rewrite gen_ifmf_eql1 in H9.



rewrite len_reg in H9; try rewrite H11; try rewrite andB_TRue_l; try rewrite gen_ifmf_eql2; try rewrite eqmeql; auto.
Focus 2. 
rewrite Example14_M. pose proof(ubEql).
apply ubEql; simpl; try rewrite Bool.andb_true_r; auto.
unfold Fresh in H0; simpl in H0. simpl in H0.
assert(occur_name_msg 1 t0 =false). 
destruct (occur_name_msg 1 t0); repeat rewrite Bool.orb_true_r in H0; repeat rewrite Bool.orb_true_l in H0; simpl in H0.
inversion H0; auto. auto.
auto.
unfold Fresh in H0; simpl in H0.
destruct (occur_name_msg 2 t1); repeat rewrite Bool.orb_true_r in H0; repeat rewrite Bool.orb_true_l in H0; simpl in H0. inversion H0. auto.
unfold Fresh in H0 |- *; simpl in H0 |- *.
assert(occur_name_msg 1 t =false).
destruct (occur_name_msg 1 t); repeat rewrite Bool.orb_true_r in H0; repeat rewrite Bool.orb_true_l in H0; simpl in H0.
inversion H0; auto. auto. simpl. rewrite H13.
auto.
unfold Fresh in H0; simpl in H0.
destruct (occur_name_msg 1 t1); repeat rewrite Bool.orb_true_r in H0; repeat rewrite Bool.orb_true_l in H0; simpl in H0.  inversion H0. auto.
(******)
unfold Fresh in H0 |- *; simpl in H0 |- *.
assert(occur_name_msg 2 t =false).
destruct (occur_name_msg 2 t); repeat rewrite Bool.orb_true_r in H0; repeat rewrite Bool.orb_true_l in H0; simpl in H0.
inversion H0; auto. auto. rewrite H13.
auto.
unfold Fresh in H0; simpl in H0.
destruct (occur_name_msg 2 t0); repeat rewrite Bool.orb_true_r in H0; repeat rewrite Bool.orb_true_l in H0; simpl in H0.  inversion H0. auto.
rewrite Example14_M.
auto.
rewrite IFTRUE_M in H9.

rewrite gen_ifmf_eql1 in H9.


rewrite len_reg in H9; try rewrite H11; try rewrite andB_TRue_l; try rewrite gen_ifmf_eql2; try rewrite eqmeql; auto.
Focus 2. 
rewrite Example14_M.
apply ubEql; simpl; try rewrite Bool.andb_true_r; auto.
unfold Fresh in H0; simpl in H0. simpl in H0.
assert(occur_name_msg 1 t0 =false). 
destruct (occur_name_msg 1 t0); repeat rewrite Bool.orb_true_r in H0; repeat rewrite Bool.orb_true_l in H0; simpl in H0.
inversion H0; auto. auto.
auto.
unfold Fresh in H0; simpl in H0.
destruct (occur_name_msg 2 t1); repeat rewrite Bool.orb_true_r in H0; repeat rewrite Bool.orb_true_l in H0; simpl in H0. inversion H0. auto.
unfold Fresh in H0 |- *; simpl in H0 |- *.
assert(occur_name_msg 1 t =false).
destruct (occur_name_msg 1 t); repeat rewrite Bool.orb_true_r in H0; repeat rewrite Bool.orb_true_l in H0; simpl in H0.
inversion H0; auto. auto. rewrite H12.
auto.
unfold Fresh in H0; simpl in H0.
destruct (occur_name_msg 1 t1); repeat rewrite Bool.orb_true_r in H0; repeat rewrite Bool.orb_true_l in H0; simpl in H0.  inversion H0. auto.
(******)
unfold Fresh in H0 |- *; simpl in H0 |- *.
assert(occur_name_msg 2 t =false).
destruct (occur_name_msg 2 t); repeat rewrite Bool.orb_true_r in H0; repeat rewrite Bool.orb_true_l in H0; simpl in H0.
inversion H0; auto. auto. rewrite H12.
auto.
unfold Fresh in H0; simpl in H0.
destruct (occur_name_msg 2 t0); repeat rewrite Bool.orb_true_r in H0; repeat rewrite Bool.orb_true_l in H0; simpl in H0.  inversion H0. auto.
rewrite Example14_M.
auto.
rewrite IFTRUE_M in H9.

(** apply ENCCCA2 :2 *)
  

pose proof (let ct:= (comm (V0 (N 0)) (kc (N 4)),
                     ub (comm (V0 (N 0)) (kc (N 4))) t r1 t5) in
                      
       let ct':= (comm (V1 (N 0)) (kc (N 3)),
                     ub (comm (V1 (N 0)) (kc (N 3))) t r0 t4) in 
                    
       let p:= |_ in let p1:=(pi1 (pi2 p), pi1 p) in let p2:= pi2 (pi2 p) in ENCCCA2 O O ct' ct O 0 11 8 8 [msg (bl c10 t r0), msg (bl c01 t r1), bol (acc c10 t r0 t4) & (acc c01 t r1 t5),
  msg
    (If (acc c10 t r0 t4) & (acc c01 t r1 t5)
        then ({ct'}_11^^7,
                   {kc (N 4) }_ 11 ^^ 9,
                   (Mvar 0,
                   {kc (N 3) }_ 11 ^^ 10)) 
        else ({p1 }_ 11 ^^ 7, {p2}_ 11 ^^ 9, ({ p1 }_ 11 ^^ 8, {p2 }_ 11 ^^ 10)))]).
simpl in H12.

(*
repeat rewrite len_reg in H12. simpl in H1.  *)
  
rewrite sub_clos with (t:=t) in H12; simpl in H1; try rewrite Bool.andb_true_r in H1; auto.
 rewrite sub_clos with (t:=t) in H12; simpl in H1; try rewrite Bool.andb_true_r in H1; auto.
rewrite Example14_M in H11. simpl.

simpl.
 
 simpl in H12.
 rewrite sub_ident with (n:=0) (t:= t4) in H12.
 rewrite sub_ident with (n:=0) (t:= t4) in H12.
 rewrite sub_ident with (n:=0) (t:= t5) in H12.
 rewrite sub_ident with (n:=0) (t:= t5) in H12. simpl in H12.
 
 

 fold (acc (comm (V1 (N 0)) (kc (N 3))) t (rb (N 1)) t4) & (acc (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2)) t5) in H12. 
 

 
rewrite gen_ifmf_eql3 in H12.


rewrite len_reg in H12; try rewrite H11; try rewrite andB_TRue_l; try rewrite gen_ifmf_eql2; try rewrite eqmeql; auto.
Focus 2.
apply ubEql; simpl; try rewrite Bool.andb_true_r; auto.
unfold Fresh in H0; simpl in H0. simpl in H0.
assert(occur_name_msg 1 t0 =false). 
destruct (occur_name_msg 1 t0); repeat rewrite Bool.orb_true_r in H0; repeat rewrite Bool.orb_true_l in H0; simpl in H0.
inversion H0; auto. auto.
auto.
unfold Fresh in H0; simpl in H0.
destruct (occur_name_msg 2 t1); repeat rewrite Bool.orb_true_r in H0; repeat rewrite Bool.orb_true_l in H0; simpl in H0. inversion H0. auto.
unfold Fresh in H0 |- *; simpl in H0 |- *.
assert(occur_name_msg 1 t =false).
destruct (occur_name_msg 1 t); repeat rewrite Bool.orb_true_r in H0; repeat rewrite Bool.orb_true_l in H0; simpl in H0.
inversion H0; auto. auto. simpl. rewrite H13.
auto.
unfold Fresh in H0; simpl in H0.
destruct (occur_name_msg 1 t1); repeat rewrite Bool.orb_true_r in H0; repeat rewrite Bool.orb_true_l in H0; simpl in H0.  inversion H0. auto.
(******)
unfold Fresh in H0 |- *; simpl in H0 |- *.
assert(occur_name_msg 2 t =false).
destruct (occur_name_msg 2 t); repeat rewrite Bool.orb_true_r in H0; repeat rewrite Bool.orb_true_l in H0; simpl in H0.
inversion H0; auto. auto. rewrite H13.
auto.
unfold Fresh in H0; simpl in H0.
destruct (occur_name_msg 2 t0); repeat rewrite Bool.orb_true_r in H0; repeat rewrite Bool.orb_true_l in H0; simpl in H0.  inversion H0. auto. simpl.
rewrite IFTRUE_M in H12.

rewrite gen_ifmf_eql3 in H12.


rewrite len_reg in H12; try rewrite H11; try rewrite andB_TRue_l; try rewrite gen_ifmf_eql2; try rewrite eqmeql; auto.
Focus 2. 

apply ubEql; simpl; try rewrite Bool.andb_true_r; auto.
unfold Fresh in H0; simpl in H0. simpl in H0.
assert(occur_name_msg 1 t0 =false). 
destruct (occur_name_msg 1 t0); repeat rewrite Bool.orb_true_r in H0; repeat rewrite Bool.orb_true_l in H0; simpl in H0.
inversion H0; auto. auto.
auto.
unfold Fresh in H0; simpl in H0.
destruct (occur_name_msg 2 t1); repeat rewrite Bool.orb_true_r in H0; repeat rewrite Bool.orb_true_l in H0; simpl in H0. inversion H0. auto.
unfold Fresh in H0 |- *; simpl in H0 |- *.
assert(occur_name_msg 1 t =false).
destruct (occur_name_msg 1 t); repeat rewrite Bool.orb_true_r in H0; repeat rewrite Bool.orb_true_l in H0; simpl in H0.
inversion H0; auto. auto. rewrite H13.
auto.
unfold Fresh in H0; simpl in H0.
destruct (occur_name_msg 1 t1); repeat rewrite Bool.orb_true_r in H0; repeat rewrite Bool.orb_true_l in H0; simpl in H0.  inversion H0. auto.
(******)
unfold Fresh in H0 |- *; simpl in H0 |- *.
assert(occur_name_msg 2 t =false).
destruct (occur_name_msg 2 t); repeat rewrite Bool.orb_true_r in H0; repeat rewrite Bool.orb_true_l in H0; simpl in H0.
inversion H0; auto. auto. rewrite H13.
auto.
unfold Fresh in H0; simpl in H0.
destruct (occur_name_msg 2 t0); repeat rewrite Bool.orb_true_r in H0; repeat rewrite Bool.orb_true_l in H0; simpl in H0.  inversion H0. auto.
rewrite IFTRUE_M in H12.






(** apply ENCCCA2 :3 **) 
fold (r 1) in H12. fold r0 in H12. fold v0 v1 k0 k1 c10 c01 (pke 11) (er 11) (r 2) r1 in H12.
pose proof (ENCCCA2 O O k1 k0 O 0 11 9 9 [msg (bl c10 t r0), msg (bl c01 t r1), bol (acc c10 t r0 t4) & (acc c01 t r1 t5),
        msg
          (If (acc c10 t r0 t4) & (acc c01 t r1 t5)
              then ((e10, (Mvar 0)), (e01, enc k0 (pke 11) (re (N 10)))) 
              else (enc (pi1 (pi2 |_), pi1 |_) (pke 11) (re (N 7)), enc (pi2 (pi2 |_)) (pke 11) (re (N 9)),
                   (enc (pi1 (pi2 |_), pi1 |_) (pke 11) (re (N 8)), enc (pi2 (pi2 |_)) (pke 11) (re (N 10)))))]).
simpl in H13.
 
rewrite sub_clos with (t:=t) in H13; simpl in H1; try rewrite Bool.andb_true_r in H1; auto.
rewrite sub_clos with (t:=t) in H13; simpl in H1; try rewrite Bool.andb_true_r in H1; auto.

rewrite sub_ident with (n:=0) (t:= t4) in H13.
 rewrite sub_ident with (n:=0) (t:= t4) in H13.
 rewrite sub_ident with (n:=0) (t:= t5) in H13.
 rewrite sub_ident with (n:=0) (t:= t5) in H13. simpl in H13.
 unfold k1, k0 in H13. 
 
 
rewrite commKeyEql with (n1:= 4) (n2:=3) in H13.
repeat rewrite IFTRUE_M in H13. 
fold (acc (comm (V1 (N 0)) (kc (N 3))) t (rb (N 1)) t4) & (acc (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2)) t5) in H13.
fold v0 v1 k0 k1 c10 c01 (pke 11) (er 11) (r 2) (r 1) r0 r1 in H13.

(** apply ENCCCA2:4 **)

pose proof(ENCCCA2 O O k0 k1 O 0 11 10 10
[msg (bl c10 t r0), msg (bl c01 t r1), bol (acc c10 t r0 t4) & (acc c01 t r1 t5),
        msg
          (If (acc c10 t r0 t4) & (acc c01 t r1 t5)
              then (enc (c10, ub c10 t r0 t4) (pke 11) (re (N 7)), {k0 }_ 11 ^^ 9,
                   (enc (c01, ub c01 t r1 t5) (pke 11) (re (N 8)), Mvar 0)) 
              else (enc (pi1 (pi2 |_), pi1 |_) (pke 11) (re (N 7)), enc (pi2 (pi2 |_)) (pke 11) (re (N 9)),
                   (enc (pi1 (pi2 |_), pi1 |_) (pke 11) (re (N 8)), enc (pi2 (pi2 |_)) (pke 11) (re (N 10)))))]).
simpl in H14.
rewrite sub_clos with (t:=t) in H14; simpl in H1; try rewrite Bool.andb_true_r in H1; auto.
rewrite sub_clos with (t:=t) in H14; simpl in H1; try rewrite Bool.andb_true_r in H1; auto.

rewrite sub_ident with (n:=0) (t:= t4) in H14.
 rewrite sub_ident with (n:=0) (t:= t4) in H14.
 rewrite sub_ident with (n:=0) (t:= t5) in H14.
 rewrite sub_ident with (n:=0) (t:= t5) in H14. simpl in H14.
 unfold k1, k0 in H14.
rewrite commKeyEql with (n1:= 3) (n2:=4) in H14.
repeat rewrite IFTRUE_M in H14. 
fold (acc (comm (V1 (N 0)) (kc (N 3))) t (rb (N 1)) t4) & (acc (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2)) t5) v0 v1 k0 k1 c10 c01 (pke 11) (er 11) (r 2) (r 1) r0 r1 in H14.

(** apply transitivity repeatedly *)
 
simpl in H10. 


fold (acc (comm (V1 (N 0)) (kc (N 3))) t (rb (N 1)) t4) & (acc (comm (V0 (N 0)) (kc (N 4))) t (rb (N 2)) t5) v0 v1 k0 k1 c10 c01 (pke 11) (er 11) (r 2) (r 1) r0 r1 in H9, H10, H12, H13, H14.


apply ext_trans with (l2:= let e1:= (c01, ub c01 t r1 t5) in let e2:= (c10, ub c10 t r0 t4) in let p:= |_ in let p':= (pi1 (pi2 p), pi1 p) in [msg (bl c10 t r0), msg (bl c01 t r1), bol (acc c10 t r0 t4) & (acc c01 t r1 t5),
        msg
          (If (acc c10 t r0 t4) & (acc c01 t r1 t5)
              then ({e1}_ 11 ^^ 7, {k1 }_ 11 ^^ 9, ({e2}_ 11 ^^ 8, {k0 }_ 11 ^^ 10)) 
              else ({p' }_ 11 ^^ 7, {pi2 (pi2 p) }_ 11 ^^ 9,
                   ({p' }_ 11 ^^ 8, {pi2 (pi2 p) }_ 11 ^^ 10)))])
                     (l3:= let e2:= (c10, ub c10 t r0 t4) in let p:= |_ in let p':= (pi1 (pi2 p), pi1 p) in [msg (bl c10 t r0), msg (bl c01 t r1), bol (acc c10 t r0 t4) & (acc c01 t r1 t5),
       msg
         (If (acc c10 t r0 t4) & (acc c01 t r1 t5)
             then ({e2 }_ 11 ^^ 7, enc k1 (pke 11) (re (N 9)),
                  (enc (c10, ub c10 t r0 t4) (pke 11) (re (N 8)), enc k0 (pke 11) (re (N 10)))) 
             else (enc (pi1 (pi2 |_), pi1 |_) (pke 11) (re (N 7)), enc (pi2 (pi2 |_)) (pke 11) (re (N 9)),
                   (enc (pi1 (pi2 |_), pi1 |_) (pke 11) (re (N 8)), enc (pi2 (pi2 |_)) (pke 11) (re (N 10)))))])
                     (l4:= let e1:= (c01, ub c01 t r1 t5) in [msg (bl c10 t r0), msg (bl c01 t r1), bol (acc c10 t r0 t4) & (acc c01 t r1 t5),
        msg
          (If (acc c10 t r0 t4) & (acc c01 t r1 t5)
              then (enc (c10, ub c10 t r0 t4) (pke 11) (re (N 7)), enc k1 (pke 11) (re (N 9)),
                   ({e1 }_ 11 ^^ 8, enc k0 (pke 11) (re (N 10)))) 
              else (enc (pi1 (pi2 |_), pi1 |_) (pke 11) (re (N 7)), enc (pi2 (pi2 |_)) (pke 11) (re (N 9)),
                    (enc (pi1 (pi2 |_), pi1 |_) (pke 11) (re (N 8)), enc (pi2 (pi2 |_)) (pke 11) (re (N 10)))))]). 
repeat split.
simpl.
apply H10;auto.  
simpl.
repeat (apply H9; try split; try unfold distMvars; simpl; try unfold t4; try unfold t5; repeat rewrite aply_f_sub with (f:=mVarMsg)). simpl. apply clos_mvars_nil in H1; try rewrite H1; auto. inversion H4; auto. inversion H4; auto. simpl.
repeat split.

repeat rewrite clos_sub_vtrm; auto. rewrite H1; auto.
unfold distMvars. inversion H4. simpl.
rewrite H15. 
auto. 
unfold distMvars. 
inversion H4. simpl.
rewrite H16. auto. simpl.

repeat rewrite Bool.andb_true_r.
simpl.  unfold c01.
simpl.
Check cca2compmsg. fold c01.
 simpl.


 unfold r0, r1.
 simpl in H6.
 
assert( cca2compmsg O O 0 11 (c01, ub c01 t r1 t5) (c10, ub c10 t r0 t4) t = true).
destruct (cca2compmsg O O 0 11 (c01, ub c01 t r1 t5) (c10, ub c10 t r0 t4) t); inversion H6; auto.
unfold t4, t5, r0, r1 in H15.
rewrite H15.
assert( cca2compmsg O O 0 11 (c01, ub c01 t r1 t5) (c10, ub c10 t r0 t4) t0 = true).
destruct (cca2compmsg O O 0 11 (c01, ub c01 t r1 t5) (c10, ub c10 t r0 t4) t0); inversion H6; auto. simpl.
unfold t4, t5, r0, r1. rewrite H15; auto.
repeat rewrite Bool.andb_true_l.
unfold t4, t5, r0, r1 in H16. 

repeat rewrite check_in_sub.
simpl.
repeat rewrite H15. simpl.

rewrite H16. simpl.
unfold t4, t5, r0, r1 in H6.
rewrite H15, H16 in H6.
assert (cca2compmsg O O 0 11 (c01, ub c01 t (r 2) {{5 := bl c10 t (r 1)}} ({{6 := bl c01 t (r 2)}} (t1)))
      (c10, ub c10 t (r 1) {{5 := bl c10 t (r 1)}} ({{6 := bl c01 t (r 2)}} (t0))) t1 = true).
destruct (cca2compmsg O O 0 11 (c01, ub c01 t (r 2) {{5 := bl c10 t (r 1)}} ({{6 := bl c01 t (r 2)}} (t1)))
    (c10, ub c10 t (r 1) {{5 := bl c10 t (r 1)}} ({{6 := bl c01 t (r 2)}} (t0))) t1).
auto. auto.
rewrite H17.
auto.

simpl.
apply H12.

repeat split.
unfold distMvars. simpl. unfold t4, t5.
repeat rewrite aply_f_sub with (f:=mVarMsg). simpl.
apply clos_mvars_nil in H1.
repeat rewrite H1; auto.
inversion H4; auto.
inversion H4; auto.
unfold t4, t5.
repeat rewrite clos_sub_vtrm; try rewrite H1; try unfold distMvars; simpl;  inversion H4; try rewrite H15; try rewrite H16; auto. simpl.

rewrite cca2comp_sym with (t:=t).
rewrite cca2comp_sym with (t:=t4).
rewrite cca2comp_sym with (t:=t5).
simpl in H6.
 
assert( cca2compmsg O O 0 11 (c01, ub c01 t r1 t5) (c10, ub c10 t r0 t4) t = true).
destruct (cca2compmsg O O 0 11 (c01, ub c01 t r1 t5) (c10, ub c10 t r0 t4) t); inversion H6; auto.
unfold t4, t5, r0, r1 in H15 |- *.
simpl.
rewrite H15.
assert( cca2compmsg O O 0 11 (c01, ub c01 t r1 t5) (c10, ub c10 t r0 t4) t0 = true).
destruct (cca2compmsg O O 0 11 (c01, ub c01 t r1 t5) (c10, ub c10 t r0 t4) t0); inversion H6; auto. simpl.
unfold t4, t5, r0, r1. rewrite H15; auto.
repeat rewrite Bool.andb_true_l.
unfold t4, t5, r0, r1 in H16.
repeat rewrite check_in_sub.
simpl.
repeat rewrite H15. simpl.

rewrite H16. simpl.
unfold t4, t5, r0, r1 in H6.
rewrite H15, H16 in H6.
assert (cca2compmsg O O 0 11 (c01, ub c01 t (r 2) {{5 := bl c10 t (r 1)}} ({{6 := bl c01 t (r 2)}} (t1)))
      (c10, ub c10 t (r 1) {{5 := bl c10 t (r 1)}} ({{6 := bl c01 t (r 2)}} (t0))) t1 = true).
destruct (cca2compmsg O O 0 11 (c01, ub c01 t (r 2) {{5 := bl c10 t (r 1)}} ({{6 := bl c01 t (r 2)}} (t1)))
    (c10, ub c10 t (r 1) {{5 := bl c10 t (r 1)}} ({{6 := bl c01 t (r 2)}} (t0))) t1).
auto. auto.
rewrite H17.
auto.



apply EQI_trans with (ml2:= ([msg (bl c10 t r0), msg (bl c01 t r1), bol (acc c10 t r0 t4) & (acc c01 t r1 t5),
         msg
           (If (acc c10 t r0 t4) & (acc c01 t r1 t5)
               then (enc (c10, ub c10 t r0 t4) (pke 11) (re (N 7)), enc k0 (pke 11) (re (N 9)),
                    (enc (c01, ub c01 t r1 t5) (pke 11) (re (N 8)), {k0 }_ 11 ^^ 10)) 
               else (enc (pi1 (pi2 |_), pi1 |_) (pke 11) (re (N 7)), enc (pi2 (pi2 |_)) (pke 11) (re (N 9)),
                    (enc (pi1 (pi2 |_), pi1 |_) (pke 11) (re (N 8)), enc (pi2 (pi2 |_)) (pke 11) (re (N 10)))))])).
apply H13.
Focus 2.
apply H14.
repeat split.
unfold t4, t5.
repeat rewrite clos_sub_vtrm; repeat rewrite aply_f_sub with (f:= mVarMsg); try rewrite H1; try unfold distMvars; simpl;  inversion H4; try rewrite H15; try rewrite H16; auto. simpl.
repeat rewrite aply_f_sub with (f:=mVarMsg); simpl in H1; simpl; try apply clos_mvars_nil in H1; try rewrite H1; auto.

simpl in H5.
 
assert( cca2compmsg O O 0 11 k0 k1 t = true).
destruct (cca2compmsg O O 0 11 k0 k1 t); inversion H5; auto.
unfold t4, t5, r0, r1 in H15 |- *.
simpl.
rewrite H15. 
assert( cca2compmsg O O 0 11 k0 k1 t0 = true). 
destruct (cca2compmsg O O 0 11 k0 k1 t0); inversion H5; auto. simpl.
unfold t4, t5, r0, r1. rewrite H15; auto.
repeat rewrite Bool.andb_true_l.
unfold t4, t5, r0, r1 in H16.
repeat rewrite check_in_sub.
simpl.
repeat rewrite H15. simpl.

rewrite H16. simpl. 
unfold t4, t5, r0, r1 in H5.
rewrite H15, H16 in H5.
assert (cca2compmsg O O 0 11 k0 k1 t1 = true).
destruct (cca2compmsg O O 0 11 k0 k1 t1).
auto. auto.
rewrite H17.
auto.


repeat split.
unfold distMvars. simpl. unfold t4, t5.
repeat rewrite aply_f_sub with (f:=mVarMsg). simpl.
apply clos_mvars_nil in H1.
repeat rewrite H1; auto.
inversion H4; auto.
inversion H4; auto.
unfold t4, t5.

 
rewrite cca2comp_sym with (t:=t).
rewrite cca2comp_sym with (t:=t4).
rewrite cca2comp_sym with (t:=t5).
simpl in H5.

assert( cca2compmsg O O 0 11 k0 k1 t = true).
destruct (cca2compmsg O O 0 11 k0 k1 t); inversion H5; auto.
unfold t4, t5, r0, r1 in H15 |- *.
simpl.
rewrite H15. 
assert( cca2compmsg O O 0 11 k0 k1 t0 = true). 
destruct (cca2compmsg O O 0 11 k0 k1 t0); inversion H5; auto. simpl.
unfold t4, t5, r0, r1. rewrite H15; auto.
repeat rewrite Bool.andb_true_l.
unfold t4, t5, r0, r1 in H16.
repeat rewrite check_in_sub.
simpl.
repeat rewrite H15. simpl.

rewrite H16. simpl. 
unfold t4, t5, r0, r1 in H5.
rewrite H15, H16 in H5.
assert (cca2compmsg O O 0 11 k0 k1 t1 = true).
destruct (cca2compmsg O O 0 11 k0 k1 t1).
auto. auto.
rewrite H17.
auto.

repeat rewrite dummy_cca2comp;auto.
  
repeat (try unfold distMvars; try unfold t4; try unfold t5; try rewrite aply_f_sub with (f:= mVarMsg); try
                                                                                                        apply clos_mvars_nil in H1; try rewrite H1; inversion H4; try rewrite H15 ;try rewrite H16; simpl; auto). 

repeat (try unfold distMvars; try unfold t4; try unfold t5; try rewrite aply_f_sub with (f:= mVarMsg); try
                                                                                                         apply clos_mvars_nil in H1; try rewrite H1; inversion H4; try rewrite H15 ;try rewrite H16; simpl; auto). 

repeat (try unfold distMvars; try unfold t4; try unfold t5; try rewrite aply_f_sub with (f:= mVarMsg); try
                                                                                                         apply clos_mvars_nil in H1; try rewrite H1; inversion H4; try rewrite H15 ;try rewrite H16; simpl; auto).


repeat (try unfold distMvars; try unfold t4; try unfold t5; try rewrite aply_f_sub with (f:= mVarMsg); try
                                                                                                         apply clos_mvars_nil in H1; try rewrite H1; inversion H4; try rewrite H15 ;try rewrite H16; simpl; auto).

repeat (try unfold distMvars; try unfold t4; try unfold t5; try rewrite aply_f_sub with (f:= mVarMsg); try
                                                                                                         apply clos_mvars_nil in H1; try rewrite H1; inversion H4; try rewrite H15 ;try rewrite H16; simpl; auto).

repeat (try unfold distMvars; try unfold t4; try unfold t5; try rewrite aply_f_sub with (f:= mVarMsg); try
                                                                                                         apply clos_mvars_nil in H1; try rewrite H1; inversion H4; try rewrite H15 ;try rewrite H16; simpl; auto).

repeat (try unfold distMvars; try unfold t4; try unfold t5; try rewrite aply_f_sub with (f:= mVarMsg); try
                                                                                                         apply clos_mvars_nil in H1; try rewrite H1; inversion H4; try rewrite H15 ;try rewrite H16; simpl; auto).
repeat (try unfold distMvars; try unfold t4; try unfold t5; try rewrite aply_f_sub with (f:= mVarMsg); try
                                                                                                         apply clos_mvars_nil in H1; try rewrite H1; inversion H4; try rewrite H15 ;try rewrite H16; simpl; auto). simpl.

repeat (try unfold distMvars; try unfold t4; try unfold t5; try rewrite aply_f_sub with (f:= mVarMsg); try
                                                                                                         apply clos_mvars_nil in H1; try rewrite H1; inversion H4; try rewrite H15 ;try rewrite H16; simpl; auto).
repeat (try unfold distMvars; try unfold t4; try unfold t5; try rewrite aply_f_sub with (f:= mVarMsg); try
                                                                                                         apply clos_mvars_nil in H1; try rewrite H1; inversion H4; try rewrite H15 ;try rewrite H16; simpl; auto).

repeat (try unfold distMvars; try unfold t4; try unfold t5; try rewrite aply_f_sub with (f:= mVarMsg); try
                                                                                                         apply clos_mvars_nil in H1; try rewrite H1; inversion H4; try rewrite H15 ;try rewrite H16; simpl; auto).
repeat (try unfold distMvars; try unfold t4; try unfold t5; try rewrite aply_f_sub with (f:= mVarMsg); try
                                                                                                         apply clos_mvars_nil in H1; try rewrite H1; inversion H4; try rewrite H15 ;try rewrite H16; simpl; auto).
repeat (try unfold distMvars; try unfold t4; try unfold t5; try rewrite aply_f_sub with (f:= mVarMsg); try
                                                                                                         apply clos_mvars_nil in H1; try rewrite H1; inversion H4; try rewrite H15 ;try rewrite H16; simpl; auto).
repeat (try unfold distMvars; try unfold t4; try unfold t5; try rewrite aply_f_sub with (f:= mVarMsg); try
                                                                                                         apply clos_mvars_nil in H1; try rewrite H1; inversion H4; try rewrite H15 ;try rewrite H16; simpl; auto).
repeat (try unfold distMvars; try unfold t4; try unfold t5; try rewrite aply_f_sub with (f:= mVarMsg); try
                                                                                                         apply clos_mvars_nil in H1; try rewrite H1; inversion H4; try rewrite H15 ;try rewrite H16; simpl; auto).
repeat (try unfold distMvars; try unfold t4; try unfold t5; try rewrite aply_f_sub with (f:= mVarMsg); try
                                                                                                         apply clos_mvars_nil in H1; try rewrite H1; inversion H4; try rewrite H15 ;try rewrite H16; simpl; auto).
 clear H9.
(********************************************************
 *********************************************************)
(*********2nd branch *******)
simpl.
apply IFBRANCH_M1 with (ml1:= [msg (bl c00 t r0), msg (bl c11 t r1), bol (acc c00 t r0 t2) & (acc c11 t r1 t3)]) (ml2:= [msg (bl c10 t r0), msg (bl c01 t r1), bol (acc c10 t r0 t4) & (acc c01 t r1 t5)]).
simpl.
unfold lt2, rt3, e00, e10, t2, t3, t4, t5.

pose proof(compHid_ext 3 4 0 1 v0 v1 [] (let u:= ( (Mvar 0), (ub (Mvar 0) t (r 1) {{5 := bl (Mvar 0) t (r 1)}} ({{6 := bl (Mvar 1) t (r 2)}} (t0)))) in [msg (bl (Mvar 0) t (r 1)), msg (bl (Mvar 1) t (r 2)),
   bol
     (acc (Mvar 0) t (r 1) {{5 := bl (Mvar 0) t (r 1)}} ({{6 := bl (Mvar 1) t (r 2)}} (t0))) &
     (acc (Mvar 1) t (r 2) {{5 := bl (Mvar 0) t (r 1)}} ({{6 := bl (Mvar 1) t (r 2)}} (t1))),
   bol (acc (Mvar 0) t (r 1) {{5 := bl (Mvar 0) t (r 1)}} ({{6 := bl (Mvar 1) t (r 2)}} (t0))),
   msg ({u }_11^^7, |_)])).
simpl in H9.  simpl in H1.

SearchAbout andb.
rewrite Bool.andb_true_r in H1.
do 4 rewrite sub_clos with (t:= t) in H9; auto.
simpl in H9. 
  
do 4 rewrite sub_in_sub with (n1:=1)(n2:= 5) in H9.

do 4 rewrite sub_in_sub with (n1:=1)(n2:= 6) in H9.
simpl in H9.

do 2  rewrite sub_clos with (t:= t) in H9; auto.

do 4 rewrite sub_in_sub with (n1:=0)(n2:= 5) in H9.

do 4 rewrite sub_in_sub with (n1:=0)(n2:= 6) in H9.
simpl in H9.

do 2 rewrite sub_clos with (t:= t) in H9; auto.
 



inversion H4.
do 4 rewrite sub_ident with (n:= 1) in H9; try rewrite H10; try rewrite H11; auto.
do 4 rewrite sub_ident with (n:= 0) in H9; try rewrite H10; try rewrite H11; auto. 
simpl in H9.
apply H9.

repeat (try split;auto).
simpl. unfold distMvars. simpl.


repeat rewrite aply_f_sub with (f:= mVarMsg); auto. simpl. 

apply clos_mvars_nil in H1; auto.  
rewrite H1; auto. unfold distMvars. simpl.
repeat rewrite aply_f_sub with (f:=mVarMsg); auto.
apply clos_mvars_nil in H1; simpl;auto. 
rewrite H1; simpl; auto.

(*** 3rd branch **)
simpl.
apply IFBRANCH_M1 with (ml1:= [msg (bl c00 t r0), msg (bl c11 t r1), bol (acc c00 t r0 t2) & (acc c11 t r1 t3), bol (acc c00 t r0 t2)]) (ml2:= [msg (bl c10 t r0), msg (bl c01 t r1), bol (acc c10 t r0 t4) & (acc c01 t r1 t5), bol (acc c10 t r0 t4)]).
simpl.
unfold lt3, rt2, t2, t3, t4, t5.
 unfold e11, e01.
 
pose proof(compHid_ext 3 4 0 1 v0 v1 [] (let u:= ((Mvar 1), ub (Mvar 1) t r1 {{5 := bl (Mvar 0) t r0}} ({{6 := bl (Mvar 1) t r1}} (t1))) in
[msg (bl (Mvar 0) t r0), msg (bl (Mvar 1) t r1),
   bol
     (acc (Mvar 0) t r0 {{5 := bl (Mvar 0) t r0}} ({{6 := bl (Mvar 1) t r1}} (t0))) &
     (acc (Mvar 1) t r1 {{5 := bl (Mvar 0) t r0}} ({{6 := bl (Mvar 1) t r1}} (t1))),
   bol (acc (Mvar 0) t r0 {{5 := bl (Mvar 0) t r0}} ({{6 := bl (Mvar 1) t r1}} (t0))),
   bol (acc (Mvar 1) t r1 {{5 := bl (Mvar 0) t r0}} ({{6 := bl (Mvar 1) t r1}} (t1))),
   msg (|_, {u }_ 11 ^^ 8)])).
simpl in H9. simpl in H1.
rewrite Bool.andb_true_r in H1.
do 4 rewrite sub_clos with (t:= t) in H9; auto.
simpl in H9. 
  
do 4 rewrite sub_in_sub with (n1:=1)(n2:= 5) in H9.

do 4 rewrite sub_in_sub with (n1:=1)(n2:= 6) in H9.
simpl in H9.

do 2  rewrite sub_clos with (t:= t) in H9; auto.

do 4 rewrite sub_in_sub with (n1:=0)(n2:= 5) in H9.

do 4 rewrite sub_in_sub with (n1:=0)(n2:= 6) in H9.
simpl in H9.

do 2 rewrite sub_clos with (t:= t) in H9; auto.
inversion H4.
do 4 rewrite sub_ident with (n:= 1) in H9; try rewrite H10; try rewrite H11; auto.
do 4 rewrite sub_ident with (n:= 0) in H9; try rewrite H10; try rewrite H11; auto. 
simpl in H9.
apply H9.

repeat (try split;auto).
simpl. unfold distMvars. simpl.
simpl. 
repeat rewrite aply_f_sub with (f:= mVarMsg); auto. simpl.
apply clos_mvars_nil in H1; auto.  
rewrite H1; auto. unfold distMvars. simpl.
repeat rewrite aply_f_sub with (f:=mVarMsg); auto.
apply clos_mvars_nil in H1; simpl;auto. 
rewrite H1; simpl; auto.

(** final *)
simpl. 
unfold t2, t3, t4, t5.
pose proof(compHid_ext 3 4 0 1 v0 v1 []
[msg (bl (Mvar 0) t r0), msg (bl (Mvar 1) t r1),
   bol
     (acc (Mvar 0) t r0 {{5 := bl (Mvar 0) t r0}} ({{6 := bl (Mvar 1) t r1}} (t0))) &
     (acc (Mvar 1) t r1 {{5 := bl (Mvar 0) t r0}} ({{6 := bl (Mvar 1) t r1}} (t1))),
   bol (acc (Mvar 0) t r0 {{5 := bl (Mvar 0) t r0}} ({{6 := bl (Mvar 1) t r1}} (t0))),
   bol (acc (Mvar 1) t r1 {{5 := bl (Mvar 0) t r0}} ({{6 := bl (Mvar 1) t r1}} (t1))), msg (|_, |_)]).
simpl in H9. simpl in H1.
rewrite Bool.andb_true_r in H1.
do 4 rewrite sub_clos with (t:= t) in H9; auto.
simpl in H9. 
  
do 4 rewrite sub_in_sub with (n1:=1)(n2:= 5) in H9.

do 4 rewrite sub_in_sub with (n1:=1)(n2:= 6) in H9.
simpl in H9.

do 2  rewrite sub_clos with (t:= t) in H9; auto.

do 4 rewrite sub_in_sub with (n1:=0)(n2:= 5) in H9.

do 4 rewrite sub_in_sub with (n1:=0)(n2:= 6) in H9.
simpl in H9.

do 2 rewrite sub_clos with (t:= t) in H9; auto.
inversion H4.
do 4 rewrite sub_ident with (n:= 1) in H9; try rewrite H10; try rewrite H11; auto.
do 4 rewrite sub_ident with (n:= 0) in H9; try rewrite H10; try rewrite H11; auto. 
simpl in H9. simpl in H9.
apply H9.

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

