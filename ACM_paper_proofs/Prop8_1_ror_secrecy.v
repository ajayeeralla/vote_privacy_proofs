(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                     Rohit Chadha <chadhar@missouri.edu>              *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)
Load "DHprotocol".
(** * Real-or-random Secrecy *)

(** This library defines proofs of real-or-random secrecy of DH protocol. 

Basically, we prove two protocols two protocols [Pi1] and [Pi2] are indistinguishable, and are defined in the file [DHprot.v].
Since all the frames in the protocols are equal except the last one, it is enough to prove the last frames [phi4] in [Pi1] and [phi24] are indistinguishable, i.e., [phi4 ~ phi24]. *)

(** Tactics to unfold various terms. *)
Ltac unf_phi := try unfold phi0, phi1, phi2, phi3, phi4, phi21, phi22, phi23, phi24;
try unfold  phi31, phi32, phi33, phi34, phi41, phi42, phi43, phi44.
Ltac unf_trm:=  try unfold  t12, t13,t14, t15,t25 , t35, t45.
Ltac unf_qa := try unfold  qa00, qa10, qa01; try unfold qa10_s, qa01_s; try unfold qa10_ss, qa01_ss; try unfold qa20, qa11; try unfold qa20_s, qa11_s;  try unfold  qa21. 
Ltac unf_qb :=  try unfold qb21, qb20_s, qb11_s; try unfold qb10_ss, qb01_ss.
Ltac unf_qc :=   try unfold qc21, qc20_s, qc11_s; try unfold qc10_ss, qc01_ss.
Ltac unf_qd :=   try unfold qd21, qd20_s, qd11_s; try unfold qd10_ss, qd01_ss.
Ltac unf := try unf_phi; try unf_trm; try unf_qa ; try unf_qb ; try unf_qc; try unf_qd.

(** A tactic to apply [RESTR] for [n] times. *)

Ltac aply_proj n n2 H := 
match n with
| 0 => idtac
| S ?n' => restrproj_in n2 H; aply_proj n' n2 H
end.  

(** To prove [phi4 ~ phi24], we first prove [phi4 ~ phi34], [phi34 ~ phi44], and [phi44 ~ phi24], where [phi34] and [phi44]
are frames of the protocols Pi2'' and Pi2' respectively. All these protocols are defined in the file [DHprot.v]. *)

Theorem Pi1_Pi2: phi4~phi24.
Proof.

(** Proof of [phi4 ~ phi34]. *)

assert( Pi1_Pi2'': phi4 ~ phi34).
repeat unf_phi. simpl.  
assert(H: (ostomsg t15) # (ostomsg t35)).
(*unfold t15, t35. simpl.
repeat rewrite andB_elm'' with (b1:= (EQ_M (to x1) (i 1)) )  (b2:= (EQ_M (act x1) new)).
assert(H3: qa01_ss  #  qc01_ss ).
unfold qa01_ss, qc01_ss.
repeat rewrite andB_elm'' with (b1:= (EQ_M (to x2) (i 1)) )  (b2:= (EQ_M (act x2) new)).
repeat unf. 
false_to_sesns 2. simpl. 
repeat redg; repeat rewrite IFTFb.
reflexivity.  
assert(H4: qa10_ss # qc10_ss).
unfold qa10_ss, qc10_ss.
assert(H5: qa20_s # qc20_s).
repeat unf.
false_to_sesns 1. simpl.
repeat redg; repeat rewrite IFTFb.
reflexivity.
assert(H6:  qa11_s # qc11_s).
  
repeat unf.
false_to_sesns 2; simpl.
unfold andB.
repeat aply_andB_elm.
aply_breq. 
repeat redg;  repeat rewrite IFTFb.
aply_breq.  
repeat redg;  repeat rewrite IFTFb. reflexivity.
*)
simpl. 
repeat unf.   
repeat rewrite andB_elm'' with (b1:= (EQ_M (to x1) (i 1)) )  (b2:= (EQ_M (act x1) new)).
false_to_sesns_all; simpl. 
repeat redg; repeat rewrite IFTFb.
aply_breq.
repeat redg;  repeat rewrite IFTFb. 
aply_breq.  
repeat redg;  repeat rewrite IFTFb.
false_to_sesns_all; simpl. 
repeat redg;  repeat rewrite IFTFb.
aply_breq.  
repeat redg;  repeat rewrite IFTFb.
false_to_sesns_all; simpl. 
repeat redg;  repeat rewrite IFTFb.
aply_breq.  
repeat redg;  repeat rewrite IFTFb.
false_to_sesns_all; simpl. 
repeat redg;  repeat rewrite IFTFb.
aply_breq.  
repeat redg;  repeat rewrite IFTFb.
repeat aply_andB_elm.
false_to_sesns_all; simpl. 
repeat redg;  repeat rewrite IFTFb.
aply_breq.  
repeat redg;  repeat rewrite IFTFb. reflexivity. 
false_to_sesns_all; simpl. 
repeat redg;  repeat rewrite IFTFb.
aply_breq.  
repeat redg;  repeat rewrite IFTFb.
aply_breq.  
repeat redg;  repeat rewrite IFTFb. reflexivity. 
false_to_sesns_all; simpl. 
repeat redg;  repeat rewrite IFTFb.
aply_breq.  
apply eqm in H. rewrite H. reflexivity.  
(** Proof of phi34 ~ phi44 .*)
assert(pi2''_pi2': phi34 ~ phi44).
repeat unf_phi. simpl. 
repeat unf. 
rewrite andB_assoc with (b2:= (EQ_M (m x2) (grn 1))).
rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))).
rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
unfold mx2rn2. 
repeat rewrite EQ_BRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) (b:=  (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
                             (EQ_M (to x2) (i 2))) & 
                            (EQ_M (to x1) (i 1))) &
                           (notb (EQ_M (act x3) new))) & 
                          (EQ_M (act x1) new)) & (EQ_M (m x3) (grn 2)))).
simpl. 
rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x4) (i 1)) &
                                 (EQ_M (to x3) (i 1))) & 
                                (EQ_M (to x2) (i 2))) & 
                               (EQ_M (to x1) (i 1))) &
                              (notb (EQ_M (act x3) new))) &
                             (EQ_M (act x1) new)) & 
                            (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))) .
unfold mx3rn1.
simpl. 
repeat rewrite EQ_BRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1)))  (b:=   (((((((EQ_M (reveal x4) (i 1)) &
                                 (EQ_M (to x3) (i 1))) & 
                                (EQ_M (to x2) (i 2))) & 
                               (EQ_M (to x1) (i 1))) &
                              (notb (EQ_M (act x3) new))) & 
                             (EQ_M (act x1) new)) & 
                            (EQ_M (m x2) (grn 1)))).
simpl.
rewrite commexp with (G:=  (pi1 (ggen (N 0)))) (g:=  (pi2 (ggen (N 0)))) (x:= (r 1)) (y:= (r 2)).
reflexivity. 
(** Proof of [phi44 ~ phi24] . *)

assert(Pi1'_Pi2: phi44 ~ phi24).
repeat unf_phi. simpl.
repeat unf.
apply  IFBRANCH_M4 with (ml1:= [msg (G 0); msg (g 0)]) (ml2:= [msg (G 0); msg (g 0)]); try  reflexivity;  simpl. 
apply IFBRANCH_M3 with (ml1:= [msg (G 0); msg (g 0); bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);  msg (grn 1)]) (ml2:= [msg (G 0); msg (g 0); bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (grn 1)]); try reflexivity; simpl.
apply IFBRANCH_M1 with (ml1:= [msg (G 0); msg (g 0); bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (grn 1); bol (EQ_M (to x2) (i 1)); msg acc;
    msg (if_then_else_M (EQ_M (to x3) (i 2)) (grn 2) O)]) (ml2:= [msg (G 0); msg (g 0); bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (grn 1); bol (EQ_M (to x2) (i 1)); msg acc;
    msg (if_then_else_M (EQ_M (to x3) (i 2)) (grn 2) O)]); try reflexivity; simpl. 

apply IFBRANCH_M1 with (ml1:=[msg (G 0); msg (g 0); bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (grn 1); bol (EQ_M (to x2) (i 1)); msg acc;
    msg (if_then_else_M (EQ_M (to x3) (i 2)) (grn 2) O);
    bol (EQ_M (to x3) (i 2))]) (ml2:=  [msg (G 0); msg (g 0); bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (grn 1); bol (EQ_M (to x2) (i 1)); msg acc;
    msg (if_then_else_M (EQ_M (to x3) (i 2)) (grn 2) O);
    bol (EQ_M (to x3) (i 2))]) ; try reflexivity; simpl.

DDH2.
(*x1**)
funapp_fm_in (i 1) DDH1.
funapp_fm_in (i 2) DDH1.
funapp_sublist_in 0 2 DDH1.
funapp_f1_in to 8 DDH1.
funapp_f2b_in EQ_M 9 6 DDH1.
funapp_f2b_in EQ_M 9 7 DDH1.
funapp_fm_in O DDH1.
funapp_f1_in act 8 DDH1.
funapp_fm_in new DDH1. 
funapp_f2b_in EQ_M 13 14 DDH1.
funapp_andB_in 10 15 DDH1.
funapp_f3bm_in (if_then_else_M) 11 4  12 DDH1.
funapp_f3bm_in (if_then_else_M) 16 3 17 DDH1.
assert((f [G 0; g 0]) # x1).
reflexivity.
rewrite H in DDH1. 

(*x2**)

reswap_in 6 18 DDH1.
reswap_in 5 6 DDH1.
reswap_in 4 5 DDH1.
reswap_in 3 4 DDH1.
funapp_sublist_in 0 3 DDH1.
restrproj_in 17 DDH1.
assert( (f [G 0; g 0; if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)  (exp (G 0) (g 0) (r 1)) (if_then_else_M (EQ_M (to x1) (i 2)) (exp (G 0) (g 0) (r 2)) O)]) # x2).
reflexivity .
rewrite H0 in DDH1.

(**x3**)

funapp_f1_in to 18 DDH1.
funapp_f2b_in EQ_M 19 17 DDH1.
funapp_f2b_in EQ_M 19 7 DDH1.
funapp_f1_in act 18 DDH1.
funapp_f2b_in EQ_M 22 14 DDH1.
funapp_andB_in 20  23  DDH1.
funapp_f3bm_in (if_then_else_M) 24 4 12  DDH1.
funapp_f3bm_in (if_then_else_M) 11 25 12  DDH1.
funapp_f3bm_in (if_then_else_M) 21 5 12  DDH1.
funapp_fm_in acc DDH1.
funapp_f3bm_in (if_then_else_M) 20 28 27  DDH1.
funapp_f3bm_in (if_then_else_M) 16 29 26  DDH1. 
reswap_in 7 30 DDH1. 
reswap_in 6 7 DDH1.
reswap_in 5 6 DDH1.
reswap_in 4 5 DDH1.
restrproj_in 29 DDH1.
restrproj_in 27 DDH1.
restrproj_in 26 DDH1.
restrproj_in 25 DDH1.
funapp_sublist_in 0 4 DDH1.
assert( (f
              [G 0; g 0;
              if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                (exp (G 0) (g 0) (r 1))
                (if_then_else_M (EQ_M (to x1) (i 2)) 
                   (exp (G 0) (g 0) (r 2)) O);
              if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                (if_then_else_M (EQ_M (to x2) (i 1)) acc
                   (if_then_else_M (EQ_M (to x2) (i 2))
                      (exp (G 0) (g 0) (r 2)) O))
                (if_then_else_M (EQ_M (to x1) (i 2))
                   (if_then_else_M (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                       (exp (G 0) (g 0) (r 1)) O) O)]) # x3). 

reflexivity. 
rewrite H1 in DDH1. 

(*x4**)

funapp_f1_in to 27 DDH1.
funapp_f2b_in EQ_M 28 17 DDH1.
funapp_f2b_in EQ_M 28 26 DDH1.
funapp_f1_in act 27 DDH1.
funapp_f2b_in EQ_M 31 14 DDH1.
(*funapp_andB_in 29 32 DDH1.*)
funapp_f3bm_in (if_then_else_M) 29 25 12  DDH1.
funapp_f3bm_in (if_then_else_M) 24 33 12  DDH1.
funapp_f3bm_in (if_then_else_M) 11 34 12  DDH1.
funapp_f1_in reveal 27 DDH1.
funapp_f2b_in EQ_M 36 17 DDH1.
funapp_f2b_in EQ_M 36 26 DDH1.
funapp_f3bm_in (if_then_else_M) 29 25 12  DDH1.
(*funapp_f3bm_in (if_then_else_M) 38 12 40  DDH1.*)
funapp_f3bm_in (if_then_else_M) 21 39 12  DDH1.
funapp_f3bm_in (if_then_else_M) 30 6 12  DDH1.
funapp_f3bm_in (if_then_else_M) 20 41 40  DDH1.
funapp_f3bm_in (if_then_else_M) 16 42 35  DDH1.
restrproj_in 42 DDH1.
restrproj_in 41 DDH1.
restrproj_in 40 DDH1.
restrproj_in 39 DDH1.
restrproj_in 38 DDH1.
restrproj_in 37 DDH1.
restrproj_in 36 DDH1.
restrproj_in 33 DDH1.
reswap_in 8 36 DDH1. 
reswap_in 7 8 DDH1. 
reswap_in 6 7 DDH1. 
reswap_in 5 6 DDH1. 
funapp_sublist_in 0 5 DDH1.
assert(  (f
              [G 0; g 0;
              if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                (exp (G 0) (g 0) (r 1))
                (if_then_else_M (EQ_M (to x1) (i 2)) 
                   (exp (G 0) (g 0) (r 2)) O);
              if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                (if_then_else_M (EQ_M (to x2) (i 1)) acc
                   (if_then_else_M (EQ_M (to x2) (i 2))
                      (exp (G 0) (g 0) (r 2)) O))
                (if_then_else_M (EQ_M (to x1) (i 2))
                   (if_then_else_M (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                      (exp (G 0) (g 0) (r 1)) O) O);
              (if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
         (if_then_else_M (EQ_M (to x2) (i 1))
            (if_then_else_M (EQ_M (to x3) (i 2)) (grn 2) O)
            (if_then_else_M (EQ_M (to x2) (i 2))
               (if_then_else_M (EQ_M (to x3) (i 1)) acc O) O))
         (if_then_else_M (EQ_M (to x1) (i 2))
            (if_then_else_M (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
               (if_then_else_M (EQ_M (to x3) (i 1)) acc O) O) O))]) # x4).
reflexivity.
rewrite H2 in DDH1.
(*****************************************************************************)
funapp_f3bm_in (if_then_else_M) 30 7 12  DDH1.
funapp_f1_in reveal 36 DDH1.
funapp_f2b_in EQ_M 38 26 DDH1.
funapp_andB_in 39 29 DDH1.
funapp_andB_in 40 21 DDH1.
funapp_andB_in 41 10 DDH1.
funapp_notB_in 32 DDH1.
funapp_andB_in 42 43 DDH1.
funapp_andB_in 44 15 DDH1.
funapp_f1_in m 18 DDH1. 
funapp_f2b_in EQ_M 46 6 DDH1.
funapp_f1_in m 27 DDH1.
funapp_f2b_in EQ_M 48 7 DDH1.
funapp_andB_in 45 47 DDH1.
funapp_andB_in 50 49 DDH1.
aply_proj 3 3 DDH1.  
aply_proj 11 35 DDH1.
aply_proj 1 35 DDH1. 
aply_proj 7 6 DDH1. 
aply_proj 3 7 DDH1. 
aply_proj 4 8 DDH1.
aply_proj 4 9 DDH1.
aply_proj 6 10 DDH1.
aply_proj 1 4 DDH1. 
aply_proj 1 10 DDH1.
reswap_in 4 5 DDH1.
reswap_in 5 6 DDH1.
reswap_in 6 7 DDH1.   
reswap_in 7 8 DDH1.   
reswap_in 6 7 DDH1.   
reswap_in 8 9 DDH1.  
reswap_in 9 10 DDH1.  
reswap_in 3 4 DDH1.  
reswap_in 6 7 DDH1.  
reswap_in 7 8 DDH1. 
rewrite commexp in DDH1.
repeat (try assumption; try reflexivity); repeat (try reflexivity).
reflexivity . reflexivity.  reflexivity.  reflexivity.  reflexivity.  

(*********************************************************************************************)
(*********************************************************************************************)
apply IFBRANCH_M1 with (ml1:= [msg (G 0); msg (g 0); bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (grn 1); bol (EQ_M (to x2) (i 1)); msg acc;
    msg (if_then_else_M (EQ_M (to x3) (i 2)) (grn 2) O);
    bol (EQ_M (to x3) (i 2));
    bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))]) (ml2:= [msg (G 0); msg (g 0); bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (grn 1); bol (EQ_M (to x2) (i 1)); msg acc;
    msg (if_then_else_M (EQ_M (to x3) (i 2)) (grn 2) O);
    bol (EQ_M (to x3) (i 2));
    bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))]) ; try reflexivity; simpl.
DDH2.

(**x1**)

funapp_fm_in (i 1) DDH1.
funapp_fm_in (i 2) DDH1.
funapp_sublist_in 0 2 DDH1.
funapp_f1_in to 8 DDH1.
funapp_f2b_in EQ_M 9 6 DDH1.
funapp_f2b_in EQ_M 9 7 DDH1.
funapp_fm_in O DDH1.
funapp_f1_in act 8 DDH1.
funapp_fm_in new DDH1. 
funapp_f2b_in EQ_M 13 14 DDH1.
funapp_andB_in 10 15 DDH1.
funapp_f3bm_in (if_then_else_M) 11 4  12 DDH1.
funapp_f3bm_in (if_then_else_M) 16 3 17 DDH1.
assert((f [G 0; g 0]) # x1).
reflexivity.
rewrite H in DDH1. 

(**x2**)

reswap_in 6 18 DDH1.
reswap_in 5 6 DDH1.
reswap_in 4 5 DDH1.
reswap_in 3 4 DDH1.
funapp_sublist_in 0 3 DDH1.
restrproj_in 17 DDH1.
assert( (f
               [G 0; g 0;
               if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                 (exp (G 0) (g 0) (r 1))
                 (if_then_else_M (EQ_M (to x1) (i 2)) 
                    (exp (G 0) (g 0) (r 2)) O)]) # x2).
reflexivity .
rewrite H0 in DDH1.

(**x3**)

funapp_f1_in to 18 DDH1.
funapp_f2b_in EQ_M 19 17 DDH1.
funapp_f2b_in EQ_M 19 7 DDH1.
funapp_f1_in act 18 DDH1.
funapp_f2b_in EQ_M 22 14 DDH1.
funapp_andB_in 20  23  DDH1.
funapp_f3bm_in (if_then_else_M) 24 4 12  DDH1.
funapp_f3bm_in (if_then_else_M) 11 25 12  DDH1.
funapp_f3bm_in (if_then_else_M) 21 5 12  DDH1.
funapp_fm_in acc DDH1.
funapp_f3bm_in (if_then_else_M) 20 28 27  DDH1.
funapp_f3bm_in (if_then_else_M) 16 29 26  DDH1. 
reswap_in 7 30 DDH1. 
reswap_in 6 7 DDH1.
reswap_in 5 6 DDH1.
reswap_in 4 5 DDH1.
restrproj_in 29 DDH1.
restrproj_in 27 DDH1.
restrproj_in 26 DDH1.
restrproj_in 25 DDH1.
funapp_sublist_in 0 4 DDH1.
assert( (f
              [G 0; g 0;
              if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                (exp (G 0) (g 0) (r 1))
                (if_then_else_M (EQ_M (to x1) (i 2)) 
                   (exp (G 0) (g 0) (r 2)) O);
              if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                (if_then_else_M (EQ_M (to x2) (i 1)) acc
                   (if_then_else_M (EQ_M (to x2) (i 2))
                      (exp (G 0) (g 0) (r 2)) O))
                (if_then_else_M (EQ_M (to x1) (i 2))
                   (if_then_else_M (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                       (exp (G 0) (g 0) (r 1)) O) O)]) # x3). 
reflexivity. 
rewrite H1 in DDH1. 

(**x4**)

funapp_f1_in to 27 DDH1.
funapp_f2b_in EQ_M 28 17 DDH1.
funapp_f2b_in EQ_M 28 26 DDH1.
funapp_f1_in act 27 DDH1.
funapp_f2b_in EQ_M 31 14 DDH1.
(*funapp_andB_in 29 32 DDH1.*)
funapp_f3bm_in (if_then_else_M) 29 25 12  DDH1.
funapp_f3bm_in (if_then_else_M) 24 33 12  DDH1.
funapp_f3bm_in (if_then_else_M) 11 34 12  DDH1.
funapp_f1_in reveal 27 DDH1.
funapp_f2b_in EQ_M 36 17 DDH1.
funapp_f2b_in EQ_M 36 26 DDH1.
funapp_f3bm_in (if_then_else_M) 29 25 12  DDH1.
(*funapp_f3bm_in (if_then_else_M) 38 12 40  DDH1.*)
funapp_f3bm_in (if_then_else_M) 21 39 12  DDH1.
funapp_f3bm_in (if_then_else_M) 30 6 12  DDH1.
funapp_f3bm_in (if_then_else_M) 20 41 40  DDH1.
funapp_f3bm_in (if_then_else_M) 16 42 35  DDH1.
restrproj_in 42 DDH1.
restrproj_in 41 DDH1.
restrproj_in 40 DDH1.
restrproj_in 39 DDH1.
restrproj_in 38 DDH1.
restrproj_in 37 DDH1.
restrproj_in 36 DDH1.
restrproj_in 33 DDH1.
reswap_in 8 36 DDH1. 
reswap_in 7 8 DDH1. 
reswap_in 6 7 DDH1. 
reswap_in 5 6 DDH1. 
funapp_sublist_in 0 5 DDH1.
assert(  (f
              [G 0; g 0;
              if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                (exp (G 0) (g 0) (r 1))
                (if_then_else_M (EQ_M (to x1) (i 2)) 
                   (exp (G 0) (g 0) (r 2)) O);
              if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                (if_then_else_M (EQ_M (to x2) (i 1)) acc
                   (if_then_else_M (EQ_M (to x2) (i 2))
                      (exp (G 0) (g 0) (r 2)) O))
                (if_then_else_M (EQ_M (to x1) (i 2))
                   (if_then_else_M (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                      (exp (G 0) (g 0) (r 1)) O) O);
              (if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
         (if_then_else_M (EQ_M (to x2) (i 1))
            (if_then_else_M (EQ_M (to x3) (i 2)) (grn 2) O)
            (if_then_else_M (EQ_M (to x2) (i 2))
               (if_then_else_M (EQ_M (to x3) (i 1)) acc O) O))
         (if_then_else_M (EQ_M (to x1) (i 2))
            (if_then_else_M (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
               (if_then_else_M (EQ_M (to x3) (i 1)) acc O) O) O))]) # x4).
reflexivity.
rewrite H2 in DDH1.
(*****************************************************************************)
(*****************************************************************************)
funapp_f3bm_in (if_then_else_M) 30 7 12  DDH1.
funapp_f1_in reveal 36 DDH1.
funapp_f2b_in EQ_M 38 26 DDH1.
funapp_andB_in 39 29 DDH1.
funapp_andB_in 40 21 DDH1.
funapp_andB_in 41 10 DDH1.
funapp_notB_in 32 DDH1.
funapp_andB_in 42 43 DDH1.
funapp_andB_in 44 15 DDH1.
funapp_f1_in m 18 DDH1. 
funapp_f2b_in EQ_M 46 6 DDH1.
funapp_f1_in m 27 DDH1.
funapp_f2b_in EQ_M 48 7 DDH1.
funapp_andB_in 45 47 DDH1.
funapp_andB_in 50 49 DDH1.
funapp_f2b_in EQ_M 38 17 DDH1.
funapp_andB_in 52 29 DDH1.
funapp_andB_in 53 21 DDH1.
funapp_andB_in 54 10 DDH1.
funapp_notB_in 32 DDH1.
funapp_andB_in 55 56 DDH1.
funapp_andB_in 57 15 DDH1.
funapp_f1_in m 18 DDH1. 
funapp_f2b_in EQ_M 59 6 DDH1.
funapp_f1_in m 27 DDH1.
funapp_f2b_in EQ_M 61 7 DDH1.
funapp_andB_in 58 60 DDH1.
funapp_andB_in 63 62 DDH1.
aply_proj 3 3 DDH1.   
aply_proj 11 35 DDH1.
aply_proj 1 35 DDH1. 
aply_proj 7 6 DDH1. 
aply_proj 3 7 DDH1. 
aply_proj 4 8 DDH1.
aply_proj 4 9 DDH1.
aply_proj 6 10 DDH1.
aply_proj 1 11 DDH1.
aply_proj 1 4 DDH1.
aply_proj 12  11 DDH1. 
reswap_in 4 5 DDH1.
reswap_in 5 6 DDH1.
reswap_in 6 7 DDH1.   
reswap_in 7 8 DDH1.   
reswap_in 6 7 DDH1.   
reswap_in 8 9 DDH1.  
reswap_in 9 10 DDH1.  
reswap_in 10 11 DDH1.  
reswap_in 6 7 DDH1.  
reswap_in 7 8 DDH1. 
rewrite commexp in DDH1.
reswap_in 3 4 DDH1.
assumption.
(**************************************************************************)
reflexivity . reflexivity.  reflexivity.  reflexivity.  reflexivity.  
(**************************************************************************)
apply IFBRANCH_M3 with (ml1:= [msg (G 0); msg (g 0); bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (grn 1); bol (EQ_M (to x2) (i 1))])(ml2:= [msg (G 0); msg (g 0); bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (grn 1); bol (EQ_M (to x2) (i 1))]);  try reflexivity; simpl.
apply IFBRANCH_M2 with (ml1:= [msg (G 0); msg (g 0); bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (grn 1); bol (EQ_M (to x2) (i 1)); bol (EQ_M (to x2) (i 2));
    msg (grn 2)]) (ml2:= [msg (G 0); msg (g 0); bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (grn 1); bol (EQ_M (to x2) (i 1)); bol (EQ_M (to x2) (i 2));
    msg (grn 2)]); try reflexivity; simpl.
apply IFBRANCH_M1 with (ml1:= [msg (G 0); msg (g 0); bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (grn 1); bol (EQ_M (to x2) (i 1)); bol (EQ_M (to x2) (i 2));
    msg (grn 2); bol (EQ_M (to x3) (i 1)); msg acc])(ml2:= [msg (G 0); msg (g 0); bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (grn 1); bol (EQ_M (to x2) (i 1)); bol (EQ_M (to x2) (i 2));
    msg (grn 2); bol (EQ_M (to x3) (i 1)); msg acc]); try reflexivity; simpl.
DDH2.
(**x1**)

funapp_fm_in (i 1) DDH1.
funapp_fm_in (i 2) DDH1.
funapp_sublist_in 0 2 DDH1.
funapp_f1_in to 8 DDH1.
funapp_f2b_in EQ_M 9 6 DDH1.
funapp_f2b_in EQ_M 9 7 DDH1.
funapp_fm_in O DDH1.
funapp_f1_in act 8 DDH1.
funapp_fm_in new DDH1. 
funapp_f2b_in EQ_M 13 14 DDH1.
funapp_andB_in 10 15 DDH1.
funapp_f3bm_in (if_then_else_M) 11 4  12 DDH1.
funapp_f3bm_in (if_then_else_M) 16 3 17 DDH1.
assert((f [G 0; g 0]) # x1).
reflexivity.
rewrite H in DDH1. 

(**x2**)

reswap_in 6 18 DDH1.
reswap_in 5 6 DDH1.
reswap_in 4 5 DDH1.
reswap_in 3 4 DDH1.
funapp_sublist_in 0 3 DDH1.
restrproj_in 17 DDH1.
assert( (f
               [G 0; g 0;
               if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                 (exp (G 0) (g 0) (r 1))
                 (if_then_else_M (EQ_M (to x1) (i 2)) 
                    (exp (G 0) (g 0) (r 2)) O)]) # x2).
reflexivity .
rewrite H0 in DDH1.

(**x3**)

funapp_f1_in to 18 DDH1.
funapp_f2b_in EQ_M 19 17 DDH1.
funapp_f2b_in EQ_M 19 7 DDH1.
funapp_f1_in act 18 DDH1.
funapp_f2b_in EQ_M 22 14 DDH1.
funapp_andB_in 20  23  DDH1.
funapp_f3bm_in (if_then_else_M) 24 4 12  DDH1.
funapp_f3bm_in (if_then_else_M) 11 25 12  DDH1.
funapp_f3bm_in (if_then_else_M) 21 5 12  DDH1.
funapp_fm_in acc DDH1.
funapp_f3bm_in (if_then_else_M) 20 28 27  DDH1.
funapp_f3bm_in (if_then_else_M) 16 29 26  DDH1. 
reswap_in 7 30 DDH1. 
reswap_in 6 7 DDH1.
reswap_in 5 6 DDH1.
reswap_in 4 5 DDH1.
restrproj_in 29 DDH1.
restrproj_in 27 DDH1.
restrproj_in 26 DDH1.
restrproj_in 25 DDH1.
funapp_sublist_in 0 4 DDH1.
(**********************************************************)
assert( (f
              [G 0; g 0;
              if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                (exp (G 0) (g 0) (r 1))
                (if_then_else_M (EQ_M (to x1) (i 2)) 
                   (exp (G 0) (g 0) (r 2)) O);
              if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                (if_then_else_M (EQ_M (to x2) (i 1)) acc
                   (if_then_else_M (EQ_M (to x2) (i 2))
                      (exp (G 0) (g 0) (r 2)) O))
                (if_then_else_M (EQ_M (to x1) (i 2))
                   (if_then_else_M (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                       (exp (G 0) (g 0) (r 1)) O) O)]) # x3). 
reflexivity. 
rewrite H1 in DDH1. 
(**x4**)
funapp_f1_in to 27 DDH1.
funapp_f2b_in EQ_M 28 17 DDH1.
funapp_f2b_in EQ_M 28 26 DDH1.
funapp_f1_in act 27 DDH1.
funapp_f2b_in EQ_M 31 14 DDH1.
(*funapp_andB_in 29 32 DDH1.*)
funapp_f3bm_in (if_then_else_M) 29 25 12  DDH1.
funapp_f3bm_in (if_then_else_M) 24 33 12  DDH1.
funapp_f3bm_in (if_then_else_M) 11 34 12  DDH1.
funapp_f1_in reveal 27 DDH1.
funapp_f2b_in EQ_M 36 17 DDH1.
funapp_f2b_in EQ_M 36 26 DDH1.
funapp_f3bm_in (if_then_else_M) 29 25 12  DDH1.
(*funapp_f3bm_in (if_then_else_M) 38 12 40  DDH1.*)
funapp_f3bm_in (if_then_else_M) 21 39 12  DDH1.
funapp_f3bm_in (if_then_else_M) 30 6 12  DDH1.
funapp_f3bm_in (if_then_else_M) 20 41 40  DDH1.
funapp_f3bm_in (if_then_else_M) 16 42 35  DDH1.
restrproj_in 42 DDH1.
restrproj_in 41 DDH1.
restrproj_in 40 DDH1.
restrproj_in 39 DDH1.
restrproj_in 38 DDH1.
restrproj_in 37 DDH1.
restrproj_in 36 DDH1.
restrproj_in 33 DDH1.
reswap_in 8 36 DDH1. 
reswap_in 7 8 DDH1. 
reswap_in 6 7 DDH1. 
reswap_in 5 6 DDH1. 
funapp_sublist_in 0 5 DDH1.
(****************************************************************)
assert(  (f
              [G 0; g 0;
              if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                (exp (G 0) (g 0) (r 1))
                (if_then_else_M (EQ_M (to x1) (i 2)) 
                   (exp (G 0) (g 0) (r 2)) O);
              if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                (if_then_else_M (EQ_M (to x2) (i 1)) acc
                   (if_then_else_M (EQ_M (to x2) (i 2))
                      (exp (G 0) (g 0) (r 2)) O))
                (if_then_else_M (EQ_M (to x1) (i 2))
                   (if_then_else_M (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                      (exp (G 0) (g 0) (r 1)) O) O);
              (if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
         (if_then_else_M (EQ_M (to x2) (i 1))
            (if_then_else_M (EQ_M (to x3) (i 2)) (grn 2) O)
            (if_then_else_M (EQ_M (to x2) (i 2))
               (if_then_else_M (EQ_M (to x3) (i 1)) acc O) O))
         (if_then_else_M (EQ_M (to x1) (i 2))
            (if_then_else_M (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
               (if_then_else_M (EQ_M (to x3) (i 1)) acc O) O) O))]) # x4).
reflexivity.
rewrite H2 in DDH1.
(****************************************************************)
funapp_f3bm_in (if_then_else_M) 30 7 12  DDH1.
funapp_f1_in reveal 36 DDH1.
funapp_f2b_in EQ_M 38 26 DDH1.
funapp_andB_in 39 29 DDH1.
funapp_andB_in 40 21 DDH1.
funapp_andB_in 41 10 DDH1.
funapp_notB_in 32 DDH1.
funapp_andB_in 42 43 DDH1.
funapp_andB_in 44 15 DDH1.
funapp_f1_in m 18 DDH1. 
funapp_f2b_in EQ_M 46 6 DDH1.
funapp_f1_in m 27 DDH1.
funapp_f2b_in EQ_M 48 7 DDH1.
funapp_andB_in 45 47 DDH1.
funapp_andB_in 50 49 DDH1.
aply_proj 3 3 DDH1.   
aply_proj 7 6 DDH1. 
aply_proj 3 7 DDH1.
aply_proj 3 9 DDH1.
aply_proj 3 10 DDH1.
aply_proj 21 11 DDH1. 
reswap_in 3 6 DDH1.
reswap_in 5 6 DDH1.
reswap_in 6 7 DDH1.   
reswap_in 7 8 DDH1.   
reswap_in 8 9 DDH1.  
reswap_in 9 10 DDH1.  
reswap_in 10 11 DDH1.  
reswap_in 4 5 DDH1. 
reswap_in 5 6 DDH1. 
reswap_in 6 7 DDH1. 
reswap_in 8 9 DDH1. 
rewrite commexp in DDH1.
assumption.
(**************************************************************************)
reflexivity . reflexivity.  reflexivity.  reflexivity.  reflexivity.  
(**************************************************************************)
apply IFBRANCH_M1 with (ml1:= [msg (G 0); msg (g 0); bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (grn 1); bol (EQ_M (to x2) (i 1)); bol (EQ_M (to x2) (i 2));
    msg (grn 2); bol (EQ_M (to x3) (i 1)); msg acc;
    bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))])(ml2:= [msg (G 0); msg (g 0); bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    msg (grn 1); bol (EQ_M (to x2) (i 1)); bol (EQ_M (to x2) (i 2));
    msg (grn 2); bol (EQ_M (to x3) (i 1)); msg acc;
    bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))]); try reflexivity; simpl.
DDH2.
(**x1**)
funapp_fm_in (i 1) DDH1.
funapp_fm_in (i 2) DDH1.
funapp_sublist_in 0 2 DDH1.
funapp_f1_in to 8 DDH1.
funapp_f2b_in EQ_M 9 6 DDH1.
funapp_f2b_in EQ_M 9 7 DDH1.
funapp_fm_in O DDH1.
funapp_f1_in act 8 DDH1.
funapp_fm_in new DDH1. 
funapp_f2b_in EQ_M 13 14 DDH1.
funapp_andB_in 10 15 DDH1.
funapp_f3bm_in (if_then_else_M) 11 4  12 DDH1.
funapp_f3bm_in (if_then_else_M) 16 3 17 DDH1.
assert((f [G 0; g 0]) # x1).
reflexivity.
rewrite H in DDH1. 
(**x2**)
reswap_in 6 18 DDH1.
reswap_in 5 6 DDH1.
reswap_in 4 5 DDH1.
reswap_in 3 4 DDH1.
funapp_sublist_in 0 3 DDH1.
restrproj_in 17 DDH1.
assert( (f
               [G 0; g 0;
               if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                 (exp (G 0) (g 0) (r 1))
                 (if_then_else_M (EQ_M (to x1) (i 2)) 
                    (exp (G 0) (g 0) (r 2)) O)]) # x2).
reflexivity .
rewrite H0 in DDH1.
(**x3**)
funapp_f1_in to 18 DDH1.
funapp_f2b_in EQ_M 19 17 DDH1.
funapp_f2b_in EQ_M 19 7 DDH1.
funapp_f1_in act 18 DDH1.
funapp_f2b_in EQ_M 22 14 DDH1.
funapp_andB_in 20  23  DDH1.
funapp_f3bm_in (if_then_else_M) 24 4 12  DDH1.
funapp_f3bm_in (if_then_else_M) 11 25 12  DDH1.
funapp_f3bm_in (if_then_else_M) 21 5 12  DDH1.
funapp_fm_in acc DDH1.
funapp_f3bm_in (if_then_else_M) 20 28 27  DDH1.
funapp_f3bm_in (if_then_else_M) 16 29 26  DDH1. 
reswap_in 7 30 DDH1. 
reswap_in 6 7 DDH1.
reswap_in 5 6 DDH1.
reswap_in 4 5 DDH1.
restrproj_in 29 DDH1.
restrproj_in 27 DDH1.
restrproj_in 26 DDH1.
restrproj_in 25 DDH1.
funapp_sublist_in 0 4 DDH1.
assert( (f
              [G 0; g 0;
              if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                (exp (G 0) (g 0) (r 1))
                (if_then_else_M (EQ_M (to x1) (i 2)) 
                   (exp (G 0) (g 0) (r 2)) O);
              if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                (if_then_else_M (EQ_M (to x2) (i 1)) acc
                   (if_then_else_M (EQ_M (to x2) (i 2))
                      (exp (G 0) (g 0) (r 2)) O))
                (if_then_else_M (EQ_M (to x1) (i 2))
                   (if_then_else_M (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                       (exp (G 0) (g 0) (r 1)) O) O)]) # x3). 

reflexivity. 
rewrite H1 in DDH1. 
(**x4***)
funapp_f1_in to 27 DDH1.
funapp_f2b_in EQ_M 28 17 DDH1.
funapp_f2b_in EQ_M 28 26 DDH1.
funapp_f1_in act 27 DDH1.
funapp_f2b_in EQ_M 31 14 DDH1.
(*funapp_andB_in 29 32 DDH1.*)
funapp_f3bm_in (if_then_else_M) 29 25 12  DDH1.
funapp_f3bm_in (if_then_else_M) 24 33 12  DDH1.
funapp_f3bm_in (if_then_else_M) 11 34 12  DDH1.
funapp_f1_in reveal 27 DDH1.
funapp_f2b_in EQ_M 36 17 DDH1.
funapp_f2b_in EQ_M 36 26 DDH1.
funapp_f3bm_in (if_then_else_M) 29 25 12  DDH1.
(*funapp_f3bm_in (if_then_else_M) 38 12 40  DDH1.*)
funapp_f3bm_in (if_then_else_M) 21 39 12  DDH1.
funapp_f3bm_in (if_then_else_M) 30 6 12  DDH1.
funapp_f3bm_in (if_then_else_M) 20 41 40  DDH1.
funapp_f3bm_in (if_then_else_M) 16 42 35  DDH1.
restrproj_in 42 DDH1.
restrproj_in 41 DDH1.
restrproj_in 40 DDH1.
restrproj_in 39 DDH1.
restrproj_in 38 DDH1.
restrproj_in 37 DDH1.
restrproj_in 36 DDH1.
restrproj_in 33 DDH1.
reswap_in 8 36 DDH1. 
reswap_in 7 8 DDH1. 
reswap_in 6 7 DDH1. 
reswap_in 5 6 DDH1. 
funapp_sublist_in 0 5 DDH1.

assert(  (f
              [G 0; g 0;
              if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                (exp (G 0) (g 0) (r 1))
                (if_then_else_M (EQ_M (to x1) (i 2)) 
                   (exp (G 0) (g 0) (r 2)) O);
              if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                (if_then_else_M (EQ_M (to x2) (i 1)) acc
                   (if_then_else_M (EQ_M (to x2) (i 2))
                      (exp (G 0) (g 0) (r 2)) O))
                (if_then_else_M (EQ_M (to x1) (i 2))
                   (if_then_else_M (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                      (exp (G 0) (g 0) (r 1)) O) O);
              (if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
         (if_then_else_M (EQ_M (to x2) (i 1))
            (if_then_else_M (EQ_M (to x3) (i 2)) (grn 2) O)
            (if_then_else_M (EQ_M (to x2) (i 2))
               (if_then_else_M (EQ_M (to x3) (i 1)) acc O) O))
         (if_then_else_M (EQ_M (to x1) (i 2))
            (if_then_else_M (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
               (if_then_else_M (EQ_M (to x3) (i 1)) acc O) O) O))]) # x4).
reflexivity.
rewrite H2 in DDH1.
(*****************************************************************************)
funapp_f3bm_in (if_then_else_M) 30 7 12  DDH1.
funapp_f1_in reveal 36 DDH1.
funapp_f2b_in EQ_M 38 26 DDH1.
funapp_andB_in 39 29 DDH1.
funapp_andB_in 40 21 DDH1.
funapp_andB_in 41 10 DDH1.
funapp_notB_in 32 DDH1.
funapp_andB_in 42 43 DDH1.
funapp_andB_in 44 15 DDH1.
funapp_f1_in m 18 DDH1. 
funapp_f2b_in EQ_M 46 6 DDH1.
funapp_f1_in m 27 DDH1.
funapp_f2b_in EQ_M 48 7 DDH1.
funapp_andB_in 45 47 DDH1.
funapp_andB_in 50 49 DDH1.
funapp_f2b_in EQ_M 38 17 DDH1.
funapp_andB_in 52 29 DDH1.
funapp_andB_in 53 21 DDH1.
funapp_andB_in 54 10 DDH1.
funapp_notB_in 32 DDH1.
funapp_andB_in 55 56 DDH1.
funapp_andB_in 57 15 DDH1.
funapp_f1_in m 18 DDH1. 
funapp_f2b_in EQ_M 59 6 DDH1.
funapp_f1_in m 27 DDH1.
funapp_f2b_in EQ_M 61 7 DDH1.
funapp_andB_in 58 60 DDH1.
funapp_andB_in 63 62 DDH1.
aply_proj 3 3 DDH1.   
aply_proj 7 6 DDH1.
aply_proj 3 7 DDH1.
aply_proj 3 9 DDH1.
aply_proj 3 10 DDH1.
aply_proj 21 11 DDH1.  
aply_proj 12 12 DDH1. 
reswap_in 4 5 DDH1.
reswap_in 5 6 DDH1.
reswap_in 6 7 DDH1.   
reswap_in 7 8 DDH1.   
reswap_in 4 5 DDH1.
reswap_in 5 6 DDH1.
reswap_in 6 7 DDH1.   
reswap_in 7 8 DDH1.   
reswap_in 8 9 DDH1.  
reswap_in 9 10 DDH1.  
reswap_in 10 11 DDH1.  
reswap_in 11 12 DDH1.  
reswap_in 3 4 DDH1.  
reswap_in 8 9 DDH1. 
rewrite commexp in DDH1.
assumption.
(**************************************************************************)
reflexivity . reflexivity.  reflexivity.  reflexivity.  reflexivity.  
(**************************************************************************)
apply IFBRANCH_M4 with (ml1:= [msg (G 0); msg (g 0); bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)]) (ml2:= [msg (G 0); msg (g 0); bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)]) ; try reflexivity; simpl.
apply IFBRANCH_M3 with (ml1:= [msg (G 0); msg (g 0); bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (to x1) (i 2)); msg (grn 2)])(ml2:= [msg (G 0); msg (g 0); bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (to x1) (i 2)); msg (grn 2)]); try reflexivity; simpl.

apply IFBRANCH_M1 with (ml1:= [msg (G 0); msg (g 0); bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (to x1) (i 2)); msg (grn 2);
    bol (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new); 
    msg (grn 1); msg (if_then_else_M (EQ_M (to x3) (i 1)) acc O)])(ml2:= [msg (G 0); msg (g 0); bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (to x1) (i 2)); msg (grn 2);
    bol (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new); 
    msg (grn 1); msg (if_then_else_M (EQ_M (to x3) (i 1)) acc O)]); try reflexivity; simpl.

apply IFBRANCH_M1 with (ml1:= ([msg (G 0); msg (g 0); bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (to x1) (i 2)); msg (grn 2);
    bol (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new); 
    msg (grn 1); msg (if_then_else_M (EQ_M (to x3) (i 1)) acc O);
    bol (EQ_M (to x3) (i 1))]))(ml2:= ([msg (G 0); msg (g 0); bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (to x1) (i 2)); msg (grn 2);
    bol (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new); 
    msg (grn 1); msg (if_then_else_M (EQ_M (to x3) (i 1)) acc O);
    bol (EQ_M (to x3) (i 1))])); try reflexivity; simpl.
DDH2.
(**x1**)
funapp_fm_in (i 1) DDH1.
funapp_fm_in (i 2) DDH1.
funapp_sublist_in 0 2 DDH1.
funapp_f1_in to 8 DDH1.
funapp_f2b_in EQ_M 9 6 DDH1.
funapp_f2b_in EQ_M 9 7 DDH1.
funapp_fm_in O DDH1.
funapp_f1_in act 8 DDH1.
funapp_fm_in new DDH1. 
funapp_f2b_in EQ_M 13 14 DDH1.
funapp_andB_in 10 15 DDH1.
funapp_f3bm_in (if_then_else_M) 11 4  12 DDH1.
funapp_f3bm_in (if_then_else_M) 16 3 17 DDH1.
assert((f [G 0; g 0]) # x1).
reflexivity.
rewrite H in DDH1. 
(***x2**)
reswap_in 6 18 DDH1.
reswap_in 5 6 DDH1.
reswap_in 4 5 DDH1.
reswap_in 3 4 DDH1.
funapp_sublist_in 0 3 DDH1.
restrproj_in 17 DDH1.
assert( (f
               [G 0; g 0;
               if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                 (exp (G 0) (g 0) (r 1))
                 (if_then_else_M (EQ_M (to x1) (i 2)) 
                    (exp (G 0) (g 0) (r 2)) O)]) # x2).
reflexivity .
rewrite H0 in DDH1.
(**x3**)
funapp_f1_in to 18 DDH1.
funapp_f2b_in EQ_M 19 17 DDH1.
funapp_f2b_in EQ_M 19 7 DDH1.
funapp_f1_in act 18 DDH1.
funapp_f2b_in EQ_M 22 14 DDH1.
funapp_andB_in 20  23  DDH1.
funapp_f3bm_in (if_then_else_M) 24 4 12  DDH1.
funapp_f3bm_in (if_then_else_M) 11 25 12  DDH1.
funapp_f3bm_in (if_then_else_M) 21 5 12  DDH1.
funapp_fm_in acc DDH1.
funapp_f3bm_in (if_then_else_M) 20 28 27  DDH1.
funapp_f3bm_in (if_then_else_M) 16 29 26  DDH1. 
reswap_in 7 30 DDH1. 
reswap_in 6 7 DDH1.
reswap_in 5 6 DDH1.
reswap_in 4 5 DDH1.
restrproj_in 29 DDH1.
restrproj_in 27 DDH1.
restrproj_in 26 DDH1.
restrproj_in 25 DDH1.
funapp_sublist_in 0 4 DDH1.
assert( (f
              [G 0; g 0;
              if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                (exp (G 0) (g 0) (r 1))
                (if_then_else_M (EQ_M (to x1) (i 2)) 
                   (exp (G 0) (g 0) (r 2)) O);
              if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                (if_then_else_M (EQ_M (to x2) (i 1)) acc
                   (if_then_else_M (EQ_M (to x2) (i 2))
                      (exp (G 0) (g 0) (r 2)) O))
                (if_then_else_M (EQ_M (to x1) (i 2))
                   (if_then_else_M (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                       (exp (G 0) (g 0) (r 1)) O) O)]) # x3). 
reflexivity. 
rewrite H1 in DDH1. 
(**x4**)
funapp_f1_in to 27 DDH1.
funapp_f2b_in EQ_M 28 17 DDH1.
funapp_f2b_in EQ_M 28 26 DDH1.
funapp_f1_in act 27 DDH1.
funapp_f2b_in EQ_M 31 14 DDH1.
(*funapp_andB_in 29 32 DDH1.*)
funapp_f3bm_in (if_then_else_M) 29 25 12  DDH1.
funapp_f3bm_in (if_then_else_M) 24 33 12  DDH1.
funapp_f3bm_in (if_then_else_M) 11 34 12  DDH1.
funapp_f1_in reveal 27 DDH1.
funapp_f2b_in EQ_M 36 17 DDH1.
funapp_f2b_in EQ_M 36 26 DDH1.
funapp_f3bm_in (if_then_else_M) 29 25 12  DDH1.
(*funapp_f3bm_in (if_then_else_M) 38 12 40  DDH1.*)
funapp_f3bm_in (if_then_else_M) 21 39 12  DDH1.
funapp_f3bm_in (if_then_else_M) 30 6 12  DDH1.
funapp_f3bm_in (if_then_else_M) 20 41 40  DDH1.
funapp_f3bm_in (if_then_else_M) 16 42 35  DDH1.
restrproj_in 42 DDH1.
restrproj_in 41 DDH1.
restrproj_in 40 DDH1.
restrproj_in 39 DDH1.
restrproj_in 38 DDH1.
restrproj_in 37 DDH1.
restrproj_in 36 DDH1.
restrproj_in 33 DDH1.
reswap_in 8 36 DDH1. 
reswap_in 7 8 DDH1. 
reswap_in 6 7 DDH1. 
reswap_in 5 6 DDH1. 
funapp_sublist_in 0 5 DDH1.
assert(  (f
              [G 0; g 0;
              if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                (exp (G 0) (g 0) (r 1))
                (if_then_else_M (EQ_M (to x1) (i 2)) 
                   (exp (G 0) (g 0) (r 2)) O);
              if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                (if_then_else_M (EQ_M (to x2) (i 1)) acc
                   (if_then_else_M (EQ_M (to x2) (i 2))
                      (exp (G 0) (g 0) (r 2)) O))
                (if_then_else_M (EQ_M (to x1) (i 2))
                   (if_then_else_M (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                      (exp (G 0) (g 0) (r 1)) O) O);
              (if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
         (if_then_else_M (EQ_M (to x2) (i 1))
            (if_then_else_M (EQ_M (to x3) (i 2)) (grn 2) O)
            (if_then_else_M (EQ_M (to x2) (i 2))
               (if_then_else_M (EQ_M (to x3) (i 1)) acc O) O))
         (if_then_else_M (EQ_M (to x1) (i 2))
            (if_then_else_M (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
               (if_then_else_M (EQ_M (to x3) (i 1)) acc O) O) O))]) # x4).
reflexivity.
rewrite H2 in DDH1.
(*****************************************************************************)
funapp_f3bm_in (if_then_else_M) 30 7 12  DDH1.
funapp_f1_in reveal 36 DDH1.
funapp_f2b_in EQ_M 38 26 DDH1.
funapp_andB_in 39 29 DDH1.
funapp_andB_in 40 21 DDH1.
funapp_andB_in 41 10 DDH1.
funapp_notB_in 32 DDH1.
funapp_andB_in 42 43 DDH1.
funapp_andB_in 44 15 DDH1.
funapp_f1_in m 18 DDH1. 
funapp_f2b_in EQ_M 46 6 DDH1.
funapp_f1_in m 27 DDH1.
funapp_f2b_in EQ_M 48 7 DDH1.
funapp_andB_in 45 47 DDH1.
funapp_andB_in 50 49 DDH1.
funapp_f3bm_in (if_then_else_M) 29 25 12  DDH1.
aply_proj 3 3 DDH1.  
aply_proj 2 6 DDH1.
aply_proj 4 7 DDH1. 
aply_proj 7 8 DDH1. 
aply_proj 4 9 DDH1. 
aply_proj 21 10 DDH1.
reswap_in 5 12 DDH1.
reswap_in 3 7 DDH1.
reswap_in 5 6 DDH1.   
reswap_in 4 5 DDH1. 
reswap_in 6 8 DDH1.   
rewrite commexp in DDH1.
assumption.
(**************************************************************************)
reflexivity . reflexivity.  reflexivity.  reflexivity.  reflexivity.  
(**************************************************************************)
apply IFBRANCH_M1 with (ml1:= [msg (G 0); msg (g 0); bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (to x1) (i 2)); msg (grn 2);
    bol (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new); 
    msg (grn 1); msg (if_then_else_M (EQ_M (to x3) (i 1)) acc O);
    bol (EQ_M (to x3) (i 1));
    bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))])(ml2:= [msg (G 0); msg (g 0); bol (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new);
    bol (EQ_M (to x1) (i 2)); msg (grn 2);
    bol (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new); 
    msg (grn 1); msg (if_then_else_M (EQ_M (to x3) (i 1)) acc O);
    bol (EQ_M (to x3) (i 1));
    bol
      (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
           (EQ_M (to x2) (i 2))) & (EQ_M (to x1) (i 1))) &
         (notb (EQ_M (act x3) new))) & (EQ_M (act x1) new)) &
       (EQ_M (m x2) (grn 1))) & (EQ_M (m x3) (grn 2))]); try reflexivity; simpl.

DDH2.
(**x1**)
funapp_fm_in (i 1) DDH1.
funapp_fm_in (i 2) DDH1.
funapp_sublist_in 0 2 DDH1.
funapp_f1_in to 8 DDH1.
funapp_f2b_in EQ_M 9 6 DDH1.
funapp_f2b_in EQ_M 9 7 DDH1.
funapp_fm_in O DDH1.
funapp_f1_in act 8 DDH1.
funapp_fm_in new DDH1. 
funapp_f2b_in EQ_M 13 14 DDH1.
funapp_andB_in 10 15 DDH1.
funapp_f3bm_in (if_then_else_M) 11 4  12 DDH1.
funapp_f3bm_in (if_then_else_M) 16 3 17 DDH1.
assert((f [G 0; g 0]) # x1).
reflexivity.
rewrite H in DDH1. 
(**x2**)
reswap_in 6 18 DDH1.
reswap_in 5 6 DDH1.
reswap_in 4 5 DDH1.
reswap_in 3 4 DDH1.
funapp_sublist_in 0 3 DDH1.
restrproj_in 17 DDH1.
assert( (f
               [G 0; g 0;
               if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                 (exp (G 0) (g 0) (r 1))
                 (if_then_else_M (EQ_M (to x1) (i 2)) 
                    (exp (G 0) (g 0) (r 2)) O)]) # x2).
reflexivity .
rewrite H0 in DDH1.
(**x3**)
funapp_f1_in to 18 DDH1.
funapp_f2b_in EQ_M 19 17 DDH1.
funapp_f2b_in EQ_M 19 7 DDH1.
funapp_f1_in act 18 DDH1.
funapp_f2b_in EQ_M 22 14 DDH1.
funapp_andB_in 20  23  DDH1.
funapp_f3bm_in (if_then_else_M) 24 4 12  DDH1.
funapp_f3bm_in (if_then_else_M) 11 25 12  DDH1.
funapp_f3bm_in (if_then_else_M) 21 5 12  DDH1.
funapp_fm_in acc DDH1.
funapp_f3bm_in (if_then_else_M) 20 28 27  DDH1.
funapp_f3bm_in (if_then_else_M) 16 29 26  DDH1. 
reswap_in 7 30 DDH1. 
reswap_in 6 7 DDH1.
reswap_in 5 6 DDH1.
reswap_in 4 5 DDH1.
restrproj_in 29 DDH1.
restrproj_in 27 DDH1.
restrproj_in 26 DDH1.
restrproj_in 25 DDH1.
funapp_sublist_in 0 4 DDH1.
assert( (f
              [G 0; g 0;
              if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                (exp (G 0) (g 0) (r 1))
                (if_then_else_M (EQ_M (to x1) (i 2)) 
                   (exp (G 0) (g 0) (r 2)) O);
              if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                (if_then_else_M (EQ_M (to x2) (i 1)) acc
                   (if_then_else_M (EQ_M (to x2) (i 2))
                      (exp (G 0) (g 0) (r 2)) O))
                (if_then_else_M (EQ_M (to x1) (i 2))
                   (if_then_else_M (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                       (exp (G 0) (g 0) (r 1)) O) O)]) # x3). 
reflexivity. 
rewrite H1 in DDH1. 
(***x4***)
funapp_f1_in to 27 DDH1.
funapp_f2b_in EQ_M 28 17 DDH1.
funapp_f2b_in EQ_M 28 26 DDH1.
funapp_f1_in act 27 DDH1.
funapp_f2b_in EQ_M 31 14 DDH1.
(*funapp_andB_in 29 32 DDH1.*)
funapp_f3bm_in (if_then_else_M) 29 25 12  DDH1.
funapp_f3bm_in (if_then_else_M) 24 33 12  DDH1.
funapp_f3bm_in (if_then_else_M) 11 34 12  DDH1.
funapp_f1_in reveal 27 DDH1.
funapp_f2b_in EQ_M 36 17 DDH1.
funapp_f2b_in EQ_M 36 26 DDH1.
funapp_f3bm_in (if_then_else_M) 29 25 12  DDH1.
(*funapp_f3bm_in (if_then_else_M) 38 12 40  DDH1.*)
funapp_f3bm_in (if_then_else_M) 21 39 12  DDH1.
funapp_f3bm_in (if_then_else_M) 30 6 12  DDH1.
funapp_f3bm_in (if_then_else_M) 20 41 40  DDH1.
funapp_f3bm_in (if_then_else_M) 16 42 35  DDH1.
restrproj_in 42 DDH1.
restrproj_in 41 DDH1.
restrproj_in 40 DDH1.
restrproj_in 39 DDH1.
restrproj_in 38 DDH1.
restrproj_in 37 DDH1.
restrproj_in 36 DDH1.
restrproj_in 33 DDH1.
reswap_in 8 36 DDH1. 
reswap_in 7 8 DDH1. 
reswap_in 6 7 DDH1. 
reswap_in 5 6 DDH1. 
funapp_sublist_in 0 5 DDH1.
assert(  (f
              [G 0; g 0;
              if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                (exp (G 0) (g 0) (r 1))
                (if_then_else_M (EQ_M (to x1) (i 2)) 
                   (exp (G 0) (g 0) (r 2)) O);
              if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
                (if_then_else_M (EQ_M (to x2) (i 1)) acc
                   (if_then_else_M (EQ_M (to x2) (i 2))
                      (exp (G 0) (g 0) (r 2)) O))
                (if_then_else_M (EQ_M (to x1) (i 2))
                   (if_then_else_M (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                      (exp (G 0) (g 0) (r 1)) O) O);
              (if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
         (if_then_else_M (EQ_M (to x2) (i 1))
            (if_then_else_M (EQ_M (to x3) (i 2)) (grn 2) O)
            (if_then_else_M (EQ_M (to x2) (i 2))
               (if_then_else_M (EQ_M (to x3) (i 1)) acc O) O))
         (if_then_else_M (EQ_M (to x1) (i 2))
            (if_then_else_M (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
               (if_then_else_M (EQ_M (to x3) (i 1)) acc O) O) O))]) # x4).
reflexivity.
rewrite H2 in DDH1.
(*****************************************************************************)
funapp_f3bm_in (if_then_else_M) 30 7 12  DDH1.
funapp_f1_in reveal 36 DDH1.
funapp_f2b_in EQ_M 38 26 DDH1.
funapp_andB_in 39 29 DDH1.
funapp_andB_in 40 21 DDH1.
funapp_andB_in 41 10 DDH1.
funapp_notB_in 32 DDH1.
funapp_andB_in 42 43 DDH1.
funapp_andB_in 44 15 DDH1.
funapp_f1_in m 18 DDH1. 
funapp_f2b_in EQ_M 46 6 DDH1.
funapp_f1_in m 27 DDH1.
funapp_f2b_in EQ_M 48 7 DDH1.
funapp_andB_in 45 47 DDH1.
funapp_andB_in 50 49 DDH1.
funapp_f2b_in EQ_M 38 17 DDH1.
funapp_andB_in 52 29 DDH1.
funapp_andB_in 53 21 DDH1.
funapp_andB_in 54 10 DDH1.
funapp_notB_in 32 DDH1.
funapp_andB_in 55 56 DDH1.
funapp_andB_in 57 15 DDH1.
funapp_f1_in m 18 DDH1. 
funapp_f2b_in EQ_M 59 6 DDH1.
funapp_f1_in m 27 DDH1.
funapp_f2b_in EQ_M 61 7 DDH1.
funapp_andB_in 58 60 DDH1.
funapp_andB_in 63 62 DDH1.
funapp_f3bm_in (if_then_else_M) 29 25 12  DDH1.
aply_proj 3 3 DDH1.   
aply_proj 2 6 DDH1.
aply_proj 4 7 DDH1. 
aply_proj 7 8 DDH1. 
aply_proj 4 9 DDH1. 
aply_proj 21 10 DDH1.
aply_proj 12 11 DDH1.
reswap_in 5 12 DDH1.
reswap_in 3 7 DDH1.
reswap_in 5 6 DDH1.
reswap_in 6 8 DDH1.   
reswap_in 4 5 DDH1.   
rewrite commexp in DDH1.
assumption.
(**************************************************************************)
reflexivity . reflexivity.  reflexivity.  reflexivity.  reflexivity.  
(**************************************************************************)
(** Apply transitivity twice to complete the proof. *)
assert(Pi1_Pi2 :  phi4~phi24).
assert(phi4~phi44).
apply EQI_trans with (ml2:= phi34). 
apply Pi1_Pi2''.  
apply pi2''_pi2'.   
 apply EQI_trans with (ml2:= phi44); repeat auto.
assumption.
Qed.
 
