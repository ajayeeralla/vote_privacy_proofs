(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                     Rohit Chadha <chadhar@missouri.edu>              *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)
Load "ex7_9".

(** Derivation of DDH assumption for three parties from two parties. [DDH] assumption for three parties:

[Fresh(G,g,a,b,c,e)-> [[G;g;g^a;g^b;g^c;g^(ab);g^(ac); g^(bc); g^(abc)]] ~ [[G;g;g^a;g^b;g^c;g^(ab);g^(ac); g^(bc); g^e]] ]. *)

Theorem Example19: forall (n n1 n2 n3 n4 n5 :nat), (Fresh [ n ; n1 ; n2 ; n3; n5 ; n4] []  = true )-> ([msg (G n); msg (g n); msg (exp (G n)(g n)(r n1)) ; msg (exp (G n)(g n)(r n2)) ; msg (exp (G n)(g n)(r n3)); msg (exp (G n)(exp (G n)(g n)(r n1)) (r n2)) ; msg (exp (G n)(exp (G n)(g n)(r n1)) (r n3)) ; msg (exp (G n)(exp (G n)(g n)(r n2)) (r n3)); msg (exp (G n)(exp (G n) (exp (G n)(g n)(r n1)) (r n2)) (r n3))])
 ~ [msg (G n); msg (g n); msg (exp (G n)(g n)(r n1)) ; msg (exp (G n)(g n)(r n2)) ; msg (exp (G n)(g n)(r n3)); msg (exp (G n)(exp (G n)(g n)(r n1)) (r n2)) ; msg (exp (G n)(exp (G n)(g n)(r n1)) (r n3)) ; msg (exp (G n)(exp (G n)(g n)(r n2)) (r n3)); msg (exp (G n)(g n)(r n5))] .
Proof.
intros.
assert (D: Fresh [n; n1; n2; n4] [] = true).
(*************proof**********)
unfold Fresh in H.
apply andb_prop with (a:=  nodup_ilist [n; n1; n2; n3; n5;n4]) (b:=  notocclist_mylist [n; n1; n2; n3; n5;n4] []) in H.
inversion H. 
unfold nodup_ilist in H0.
 unfold count_occur in H0.
 rewrite <- beq_nat_refl in H0.
assert(H2: beq_nat n1 n = false).
Fr_pf. 
assert(H3: beq_nat n2 n = false).
  Fr_pf. 
assert(H4: beq_nat n3 n = false).
Fr_pf. 
assert(H5: beq_nat n5 n = false).
Fr_pf.
assert(H6: beq_nat n4 n = false).
Fr_pf.
assert(H7: beq_nat n2 n1 = false).
Fr_pf.
assert(H8: beq_nat n3 n1 = false ).
Fr_pf.
assert(H9: beq_nat n5 n1 = false).
Fr_pf.
assert(H10 : beq_nat n4 n1 = false).
Fr_pf.
assert(H11: beq_nat n3 n2 = false).
Fr_pf.
assert(H12: beq_nat n5 n2 = false).
Fr_pf.
assert(H13: beq_nat n4 n2 = false).
Fr_pf.
assert(H14: beq_nat n5 n3 = false).
Fr_pf.
(*******************************************************)
rew_all_hyps.
(****************************************************************)
apply DDH in D.
(******step3**************)
assert(Fresh3: Fresh [n3 ] ([msg (G  n); msg (g  n);
      msg (exp (G n)(g n)(r n1));
msg (exp (G n)(g n)(r n2));
     msg (exp (G  n)
        (exp (G n)(g n)(r n1)) (r n2))] ++
     [msg (G n); msg (g n);
    msg  (exp (G n)(g n)(r n1));
   msg  (exp (G n)(g n)(r n2));
     msg (exp (G n)(g n)(r n4))]) = true) .
(********proof***********)
unfold Fresh in H.
apply andb_prop with (a:=  nodup_ilist [n; n1; n2; n3; n5;n4]) (b:=  notocclist_mylist [n; n1; n2; n3; n5;n4] []) in H.
inversion H. 
unfold nodup_ilist in H0.
 unfold count_occur in H0.
 rewrite <- beq_nat_refl in H0.
assert(H2: beq_nat n1 n = false).
Fr_pf.
assert(H3: beq_nat n2 n = false).
Fr_pf.
assert(H4: beq_nat n3 n = false).
Fr_pf.
assert(H5: beq_nat n5 n = false).
Fr_pf.
assert(H6: beq_nat n4 n = false).
Fr_pf.
assert(H7: beq_nat n2 n1 = false).
Fr_pf.
assert(H8: beq_nat n3 n1 = false ).
Fr_pf.
assert(H9: beq_nat n5 n1 = false).
Fr_pf.
assert(H10 : beq_nat n4 n1 = false).
Fr_pf.
assert(H11: beq_nat n3 n2 = false).
Fr_pf.
assert(H12: beq_nat n5 n2 = false).
Fr_pf.
assert(H13: beq_nat n4 n2 = false).
Fr_pf.
assert(H14: beq_nat n5 n3 = false).
Fr_pf.
assert(H15: beq_nat n4 n3 = false).
Fr_pf.
(**********************) 
rew_all_hyps.
 rewrite <- Nat.eqb_sym.  rew_all_hyps. rewrite <- Nat.eqb_sym.  rew_all_hyps. rewrite <- Nat.eqb_sym.  rew_all_hyps.
(******************************************************)
assert(s4: (clos_mylist([msg (G n); msg (g n);
 msg (exp (G n)(g n)(r n1));
        msg (exp (G n)(g n)(r n2));
        msg (exp (G n)
          (exp (G n)(g n)(r n1)) (r n2))] ++
        [msg (G n);msg (g n);
        msg (exp (G n)(g n)(r n1));
        msg (exp (G n)(g n)(r n2));
        msg (exp (G n)(g n)(r n4))] )= true) /\ ( Fresh [n3]
       ([ msg (G n); msg (g n);
        msg (exp (G n)(g n)(r n1));
        msg (exp (G n)(g n)(r n2));
       msg ( exp (G n)
          (exp (G n)(g n)(r n1)) (r n2))] ++
        [msg (G n); msg ( g n);
        msg (exp (G n)(g n)(r n1));
        msg (exp (G n)(g n)(r n2));
        msg (exp (G n)(g n)(r n4))]) = true)
/\( Fresh [n3]
       ([ msg (G n); msg (g n);
        msg (exp (G n)(g n)(r n1));
        msg (exp (G n)(g n)(r n2));
       msg ( exp (G n)
          (exp (G n)(g n)(r n1)) (r n2))] ++
        [msg (G n); msg ( g n);
        msg (exp (G n)(g n)(r n1));
        msg (exp (G n)(g n)(r n2));
        msg (exp (G n)(g n)(r n4))]) = true)
/\ ([msg (G n); msg (g n);
      msg (exp (G n)(g n)(r n1));
      msg (exp (G n)(g n)(r n2));
      msg (exp (G n)
        (exp (G n)(g n)(r n1)) (r n2))]) ~
     [msg (G n); msg  (g n);
     msg (exp (G n)(g n)(r n1));
     msg (exp (G n)(g n)(r n2));
     msg (exp (G n)(g n)(r n4))]).

repeat (try split); repeat (try reflexivity);
auto.
apply FRESHIND with (n1:=n3) (n2:=n3) in s4 .
simpl in s4.

(*******construct term from terms in list and append *****************)
funapp_exp_in  2 3 1 s4.
funapp_exp_in 2 4 1 s4.
funapp_exp_in 2 5 1 s4.
funapp_exp_in 2 6 1 s4.
dropone_in s4.
assert(DDH2: Fresh [n;n4;n3;n5] [] = true).
(***********proof**********************)
unfold Fresh in H.
apply andb_prop with (a:=  nodup_ilist [n; n1; n2; n3; n5;n4]) (b:=  notocclist_mylist [n; n1; n2; n3; n5;n4] []) in H.
inversion H. 
unfold nodup_ilist in H0.
 unfold count_occur in H0.
 rewrite <- beq_nat_refl in H0.
assert(H2: beq_nat n1 n = false).
Fr_pf.
assert(H3: beq_nat n2 n = false).
Fr_pf.
assert(H4: beq_nat n3 n = false).
Fr_pf.
assert(H5: beq_nat n5 n = false).
Fr_pf.
assert(H6: beq_nat n4 n = false).
Fr_pf.
assert(H7: beq_nat n2 n1 = false).
Fr_pf.
assert(H8: beq_nat n3 n1 = false ).
Fr_pf.
assert(H9: beq_nat n5 n1 = false).
Fr_pf.
assert(H10 : beq_nat n4 n1 = false).
Fr_pf.
assert(H11: beq_nat n3 n2 = false).
Fr_pf.
assert(H12: beq_nat n5 n2 = false).
Fr_pf.
assert(H13: beq_nat n4 n2 = false).
Fr_pf.
assert(H14: beq_nat n5 n3 = false).
Fr_pf.
assert(H15: beq_nat n4 n3 = false).
Fr_pf.
assert(H16: beq_nat n4 n5 = false).
Fr_pf.
(**********************)
rew_all_hyps. rewrite <- Nat.eqb_sym. rew_all_hyps. rewrite <- Nat.eqb_sym. rew_all_hyps.
rewrite <- Nat.eqb_sym. rew_all_hyps.
(****************************************)
apply DDH in DDH2. 
assert(Fresh [n2] ([msg (G n); msg (g n);
 msg   (   exp (G n)(g n)(r n4));
     msg ( exp (G n)(g n)(r n3));
     msg (exp (G n)
        (exp (G n)(g n)(r n4)) (r n3))]++[ msg (G n); msg ( g n);
     msg (exp (G n)(g n)(r n4));
    msg (exp (G n)(g n)(r n3));
     msg (exp (G n)(g n)(r n5))]) = true).
(********proof***********)
unfold Fresh in H.
apply andb_prop with (a:=  nodup_ilist [n; n1; n2; n3; n5;n4]) (b:=  notocclist_mylist [n; n1; n2; n3; n5;n4] []) in H.
inversion H. 
unfold nodup_ilist in H0.
 unfold count_occur in H0.
 rewrite <- beq_nat_refl in H0.

assert(H2: beq_nat n1 n = false).
Fr_pf.
assert(H3: beq_nat n2 n = false).
Fr_pf.
assert(H4: beq_nat n3 n = false).
Fr_pf.
assert(H5: beq_nat n5 n = false).
Fr_pf.
assert(H6: beq_nat n4 n = false).
Fr_pf.
assert(H7: beq_nat n2 n1 = false).
Fr_pf.
assert(H8: beq_nat n3 n1 = false ).
Fr_pf.
assert(H9: beq_nat n5 n1 = false).
Fr_pf.
assert(H10 : beq_nat n4 n1 = false).
Fr_pf.
assert(H11: beq_nat n3 n2 = false).
Fr_pf.
assert(H12: beq_nat n5 n2 = false).
Fr_pf.
assert(H13: beq_nat n4 n2 = false).
Fr_pf.
assert(H14: beq_nat n5 n3 = false).
Fr_pf.
assert(H15: beq_nat n4 n3 = false).
Fr_pf.
(**********************)
rew_all_hyps. 
 rewrite <- Nat.eqb_sym. rew_all_hyps.
(*********************************************************)
assert(line7: (clos_mylist ([msg (G n); msg (g n);
      msg (exp (G n)(g n)(r n4));
      msg (exp (G n)(g n)(r n3));
      msg (exp (G n)
        (exp (G n)(g n)(r n4)) (r n3))]++[msg (G n); msg (g n);
     msg (exp (G n)(g n)(r n4));
     msg (exp (G n)(g n)(r n3));
     msg (exp (G n)(g n)(r n5))]) = true) /\
(Fresh [n2] ([msg (G n); msg (g n);
 msg   (   exp (G n)(g n)(r n4));
     msg ( exp (G n)(g n)(r n3));
     msg (exp (G n)
        (exp (G n)(g n)(r n4)) (r n3))] ++ [ msg (G n); msg ( g n);
     msg (exp (G n)(g n)(r n4));
    msg (exp (G n)(g n)(r n3));
     msg (exp (G n)(g n)(r n5))]) = true) /\ (Fresh [n2] ([msg (G n); msg (g n);
 msg   (   exp (G n)(g n)(r n4));
     msg ( exp (G n)(g n)(r n3));
     msg (exp (G n)
        (exp (G n)(g n)(r n4)) (r n3))]++[ msg (G n); msg ( g n);
     msg (exp (G n)(g n)(r n4));
    msg (exp (G n)(g n)(r n3));
     msg (exp (G n)(g n)(r n5))]) = true) /\ [msg (G n); msg (g n);
      msg (exp (G n)(g n)(r n4));
      msg (exp (G n)(g n)(r n3));
      msg (exp (G n)
        (exp (G n)(g n)(r n4)) (r n3))] ~
     [msg (G n); msg (g n);
     msg (exp (G n)(g n)(r n4));
    msg (exp (G n)(g n)(r n3));
     msg (exp (G n)(g n)(r n5))]).
repeat (try split); repeat (try reflexivity); auto.

apply FRESHIND with (n1:=n2) (n2:=n2) in line7 .
simpl in line7. clear H0.

assert(Fresh1 : ( Fresh [n1] ([msg (r n2); msg (G n); msg (g n);
        msg (exp (G n)(g n)(r n4));
         msg (exp (G n)(g n)(r n3));
         msg (exp (G n)
           (exp (G n)(g n)(r n4)) (r n3))] ++
        [msg (r n2); msg (G n); msg (g n);
        msg (exp (G n)(g n)(r n4));
       msg (exp (G n)(g n)(r n3));
        msg (exp (G n)(g n)(r n5))]) = true)).

(*****proof**********************************************)
(********proof***********)
unfold Fresh in H.
apply andb_prop with (a:=  nodup_ilist [n; n1; n2; n3; n5;n4]) (b:=  notocclist_mylist [n; n1; n2; n3; n5;n4] []) in H.
inversion H. 
unfold nodup_ilist in H0.
 unfold count_occur in H0.
 rewrite <- beq_nat_refl in H0.

assert(H2: beq_nat n1 n = false).
Fr_pf.
assert(H3: beq_nat n2 n = false).
Fr_pf.
assert(H4: beq_nat n3 n = false).
Fr_pf.

assert(H5: beq_nat n5 n = false).
Fr_pf.
assert(H6: beq_nat n4 n = false).
Fr_pf.
assert(H7: beq_nat n2 n1 = false).
Fr_pf.
assert(H8: beq_nat n3 n1 = false ).
Fr_pf.
assert(H9: beq_nat n5 n1 = false).
Fr_pf.
assert(H10 : beq_nat n4 n1 = false).
Fr_pf.
assert(H11: beq_nat n3 n2 = false).
Fr_pf.
assert(H12: beq_nat n5 n2 = false).
Fr_pf.
assert(H13: beq_nat n4 n2 = false).
Fr_pf.

assert(H14: beq_nat n5 n3 = false).
Fr_pf.
assert(H15: beq_nat n4 n3 = false).
Fr_pf.

(**********************)
rew_all_hyps. rewrite <- Nat.eqb_sym. rew_all_hyps.
(***************************************************)
(***************************************************)
assert(temp2:(clos_mylist ([msg (r n2); msg (G n); msg (g n);
         msg (exp (G n)(g n)(r n4));
         msg (exp (G n)(g n)(r n3));
         msg (exp (G n)
           (exp (G n)(g n)(r n4)) (r n3))] ++
        [msg (r n2); msg (G n); msg (g n);
        msg (exp (G n)(g n)(r n4));
        msg (exp (G n)(g n)(r n3));
        msg (exp (G n)(g n)(r n5))]) = true)/\( Fresh [n1] ([msg (r n2); msg (G n); msg (g n);
        msg (exp (G n)(g n)(r n4));
         msg (exp (G n)(g n)(r n3));
         msg (exp (G n)
           (exp (G n)(g n)(r n4)) (r n3))] ++
        [msg (r n2); msg (G n); msg (g n);
        msg (exp (G n)(g n)(r n4));
       msg (exp (G n)(g n)(r n3));
        msg (exp (G n)(g n)(r n5))]) = true) /\ 
( Fresh [n1] ([msg (r n2); msg (G n); msg (g n);
        msg (exp (G n)(g n)(r n4));
         msg (exp (G n)(g n)(r n3));
         msg (exp (G n)
           (exp (G n)(g n)(r n4)) (r n3))] ++
        [msg (r n2); msg (G n); msg (g n);
        msg (exp (G n)(g n)(r n4));
       msg (exp (G n)(g n)(r n3));
        msg (exp (G n)(g n)(r n5))]) = true) /\
[msg (r n2); msg (G n); msg (g n);
       msg (  exp (G n)(g n)(r n4));
       msg ( exp (G n)(g n)(r n3));
        msg (exp (G n)
           (exp (G n)(g n)(r n4)) (r n3))] ~
        [msg (r n2); msg (G n); msg (g n);
        msg (exp (G n)(g n)(r n4));
       msg (exp (G n)(g n)(r n3));
        msg (exp (G n)(g n)(r n5))]).

repeat (try split); repeat (try reflexivity); auto.

apply FRESHIND with (n1:= n1) (n2:= n1) in temp2.
simpl in temp2.

(*******construct term from terms in list and append *****************)

funapp_exp_in 3 4 1 temp2.
funapp_exp_in 3 4 2 temp2.
funapp_exp_in 3 6 1 temp2.
funapp_exp_in 3 6 2 temp2.
(*rewrite IFTRUE_M *)
rewrite commexp with (G:= (G n))(g:= g n)(x := (r n3))(y:= (r n1)) in temp2.
rewrite commexp with (G:= (G n))(g:= g n)(x := (r n3))(y:= (r n2)) in temp2.
(*******drop 2 elements***************)
aply_in 2 dropone_in temp2.
(********************RESTR2***********************)
restr_swap_in 5 6 temp2.
restr_swap_in 6 7 temp2.
restr_swap_in 4 5 temp2.
restr_swap_in 3 4 temp2.
restr_swap_in 5 6 temp2.
restr_swap_in 4 5 temp2.
restr_swap_in 7 8 temp2.
restr_swap_in 8 9 temp2.
assert(line10: [msg (G n); msg (g n);
        msg (exp (G n)(g n)(r n1));
        msg (exp (G n)(g n)(r n2));
        msg (exp (G n)(exp (G n)(g n)(r n1)) (r n2));
        msg (exp (G n)(g n)(r n3));
        msg (exp (G n)(exp (G n)(g n)(r n1)) (r n3));
        msg (exp (G n)(exp (G n)(g n)(r n2)) (r n3));
        msg
          (exp (G n)
             (exp (G n)(exp (G n)(g n)(r n1)) (r n2))
             (r n3))] ~   [msg (G n); msg (g n);
          msg (exp (G n)(g n)(r n1));
          msg (exp (G n)(g n)(r n2));
          msg (exp (G n)(g n)(r n4));
          msg (exp (G n)(g n)(r n3));
          msg (exp (G n)(exp (G n)(g n)(r n1)) (r n3));
          msg (exp (G n)(exp (G n)(g n)(r n2)) (r n3));
          msg (exp (G n)(g n)(r n5))]).

apply EQI_trans with (ml2:= [msg (G n); msg (g n);
       msg (exp (G n)(g n)(r n1));
       msg (exp (G n)(g n)(r n2));
       msg (exp (G n)(g n)(r n4));
       msg (exp (G n)(g n)(r n3));
       msg (exp (G n)(exp (G n)(g n)(r n1)) (r n3));
       msg (exp (G n)(exp (G n)(g n)(r n2)) (r n3));
       msg (exp (G n)(exp (G n)(g n)(r n4)) (r n3))] ). apply s4. apply temp2.
assert(Fresh5: ( Fresh [n5] ( [msg (G n); msg (g n);
       msg (exp (G n)(g n)(r n1));
       msg (exp (G n)(g n)(r n2));
       msg (exp (G n)(exp (G n)(g n)(r n1)) (r n2))] ++
          [msg (G n); msg (g n);
      msg (exp (G n)(g n)(r n1));
      msg (exp (G n)(g n)(r n2));
      msg (exp (G n)(g n)(r n4))]) = true)).
(*****************************************************)
(*****proof**********************************************)
(***********proof**********************)
unfold Fresh in H.
apply andb_prop with (a:=  nodup_ilist [n; n1; n2; n3; n5;n4]) (b:=  notocclist_mylist [n; n1; n2; n3; n5;n4] []) in H.
inversion H. 
unfold nodup_ilist in H0.
 unfold count_occur in H0.
 rewrite <- beq_nat_refl in H0.
assert(H2: beq_nat n1 n = false).
Fr_pf.
assert(H3: beq_nat n2 n = false).
Fr_pf.
assert(H4: beq_nat n3 n = false).
Fr_pf.
assert(H5: beq_nat n5 n = false).
Fr_pf.
assert(H6: beq_nat n4 n = false).
Fr_pf.
assert(H7: beq_nat n2 n1 = false).
Fr_pf.
assert(H8: beq_nat n3 n1 = false ).
Fr_pf.
assert(H9: beq_nat n5 n1 = false).
Fr_pf.
assert(H10 : beq_nat n4 n1 = false).
Fr_pf.
assert(H11: beq_nat n3 n2 = false).
Fr_pf.
assert(H12: beq_nat n5 n2 = false).
Fr_pf.
assert(H13: beq_nat n4 n2 = false).
Fr_pf.
assert(H14: beq_nat n5 n3 = false).
Fr_pf.
assert(H15: beq_nat n4 n3 = false).
Fr_pf.
assert(H16: beq_nat n4 n5 = false).
Fr_pf.
(**********************)
rew_all_hyps.
 rewrite <- Nat.eqb_sym. rew_all_hyps.
  rewrite <- Nat.eqb_sym.  rew_all_hyps.
rewrite <- Nat.eqb_sym.  rew_all_hyps.
(***************************************************)
(***************************************************)
assert(s11: (clos_mylist([msg (G n); msg (g n);
 msg (exp (G n)(g n)(r n1));
        msg (exp (G n)(g n)(r n2));
        msg (exp (G n)
          (exp (G n)(g n)(r n1)) (r n2))] ++
        [msg (G n);msg (g n);
        msg (exp (G n)(g n)(r n1));
        msg (exp (G n)(g n)(r n2));
        msg (exp (G n)(g n)(r n4))] )= true) /\ ( Fresh [n5]
       ([ msg (G n); msg (g n);
        msg (exp (G n)(g n)(r n1));
        msg (exp (G n)(g n)(r n2));
       msg ( exp (G n)
          (exp (G n)(g n)(r n1)) (r n2))] ++
        [msg (G n); msg ( g n);
        msg (exp (G n)(g n)(r n1));
        msg (exp (G n)(g n)(r n2));
        msg (exp (G n)(g n)(r n4))]) = true)
/\( Fresh [n5]
       ([ msg (G n); msg (g n);
        msg (exp (G n)(g n)(r n1));
        msg (exp (G n)(g n)(r n2));
       msg ( exp (G n)
          (exp (G n)(g n)(r n1)) (r n2))] ++
        [msg (G n); msg ( g n);
        msg (exp (G n)(g n)(r n1));
        msg (exp (G n)(g n)(r n2));
        msg (exp (G n)(g n)(r n4))]) = true)
/\ ([msg (G n); msg (g n);
      msg (exp (G n)(g n)(r n1));
      msg (exp (G n)(g n)(r n2));
      msg (exp (G n)
        (exp (G n)(g n)(r n1)) (r n2))]) ~
     [msg (G n); msg  (g n);
     msg (exp (G n)(g n)(r n1));
     msg (exp (G n)(g n)(r n2));
     msg (exp (G n)(g n)(r n4))]).
repeat (try split); repeat (try reflexivity); auto.
apply FRESHIND with (n1:= n5) (n2:= n5) in s11.
simpl in s11.
clear Fresh3.
assert(Fresh3:( Fresh [n3] ( [msg (r n5); msg (G n); msg (g n);
         msg (exp (G n)(g n)(r n1));
         msg (exp (G n)(g n)(r n2));
         msg (exp (G n)(exp (G n)(g n)(r n1)) (r n2))] ++  [msg (r n5); msg (G n); msg (g n);
        msg (exp (G n)(g n)(r n1));
        msg (exp (G n)(g n)(r n2));
        msg (exp (G n)(g n)(r n4))]) = true)).
(*********************proof************************************)
unfold Fresh in H.
apply andb_prop with (a:=  nodup_ilist [n; n1; n2; n3; n5;n4]) (b:=  notocclist_mylist [n; n1; n2; n3; n5;n4] []) in H.
inversion H. 
unfold nodup_ilist in H0.
 unfold count_occur in H0.
 rewrite <- beq_nat_refl in H0.
assert(H2: beq_nat n1 n = false).
Fr_pf.
assert(H3: beq_nat n2 n = false).
Fr_pf.
assert(H4: beq_nat n3 n = false).
Fr_pf.
assert(H5: beq_nat n5 n = false).
Fr_pf.
assert(H6: beq_nat n4 n = false).
Fr_pf.
assert(H7: beq_nat n2 n1 = false).
Fr_pf.
assert(H8: beq_nat n3 n1 = false ).
Fr_pf.
assert(H9: beq_nat n5 n1 = false).
Fr_pf.
assert(H10 : beq_nat n4 n1 = false).
Fr_pf.
assert(H11: beq_nat n3 n2 = false).
Fr_pf.
assert(H12: beq_nat n5 n2 = false).
Fr_pf.
assert(H13: beq_nat n4 n2 = false).
Fr_pf.
assert(H14: beq_nat n5 n3 = false).
Fr_pf.
assert(H15: beq_nat n4 n3 = false).
Fr_pf.
(**********************)
rew_all_hyps.  rewrite <- Nat.eqb_sym. rew_all_hyps. rewrite <- Nat.eqb_sym. rew_all_hyps.  rewrite <- Nat.eqb_sym. rew_all_hyps.
assert(temp3:(clos_mylist ([msg (r n5); msg (G n); msg (g n);
         msg (exp (G n)(g n)(r n1));
         msg (exp (G n)(g n)(r n2));
         msg (exp (G n)(exp (G n)(g n)(r n1)) (r n2))] ++
        [msg (r n5); msg (G n); msg (g n);
        msg (exp (G n)(g n)(r n1));
        msg (exp (G n)(g n)(r n2));
        msg (exp (G n)(g n)(r n4))]) = true) /\( Fresh [n3] ( [msg (r n5); msg (G n); msg (g n);
         msg (exp (G n)(g n)(r n1));
         msg (exp (G n)(g n)(r n2));
         msg (exp (G n)(exp (G n)(g n)(r n1)) (r n2))] ++  [msg (r n5); msg (G n); msg (g n);
        msg (exp (G n)(g n)(r n1));
        msg (exp (G n)(g n)(r n2));
        msg (exp (G n)(g n)(r n4))]) = true) /\
( Fresh [n3] ( [msg (r n5); msg (G n); msg (g n);
         msg (exp (G n)(g n)(r n1));
         msg (exp (G n)(g n)(r n2));
         msg (exp (G n)(exp (G n)(g n)(r n1)) (r n2))] ++  [msg (r n5); msg (G n); msg (g n);
        msg (exp (G n)(g n)(r n1));
        msg (exp (G n)(g n)(r n2));
        msg (exp (G n)(g n)(r n4))]) = true)
       /\ ([msg (r n5); msg (G n); msg (g n);
         msg (exp (G n)(g n)(r n1));
         msg (exp (G n)(g n)(r n2));
         msg (exp (G n)(exp (G n)(g n)(r n1)) (r n2))]) ~
        [msg (r n5); msg (G n); msg (g n);
        msg (exp (G n)(g n)(r n1));
        msg (exp (G n)(g n)(r n2));
        msg (exp (G n)(g n)(r n4))]).
repeat (try split); repeat (try reflexivity); auto.
apply FRESHIND with (n1:= n3) (n2:= n3) in temp3.
simpl in temp3.
(*******construct term from terms in list and append *****************)
funapp_exp_in 3 4 1 temp3.
funapp_exp_in 3 4 2 temp3.
funapp_exp_in 3 5 1 temp3.
funapp_exp_in 3 6 1 temp3.
(**********drop two elts ********************)
aply_in 2 dropone_in temp3.
restr_swap_in 7 8 temp3.
restr_swap_in 8 9 temp3.
assert(Final :[msg (G n); msg (g n);
            msg (exp (G n)(g n)(r n1));
            msg (exp (G n)(g n)(r n2));
            msg
              (exp (G n)(exp (G n)(g n)(r n1)) (r n2));
            msg (exp (G n)(g n)(r n3));
            msg
              (exp (G n)(exp (G n)(g n)(r n1)) (r n3));
            msg
              (exp (G n)(exp (G n)(g n)(r n2)) (r n3));
            msg
              (exp (G n)
                 (exp (G n)(exp (G n)(g n)(r n1))
                    (r n2)) (r n3))] ~ [msg (G n); msg (g n);
           msg (exp (G n)(g n)(r n1));
           msg (exp (G n)(g n)(r n2));
           msg
             (exp (G n)(exp (G n)(g n)(r n1)) (r n2));
           msg (exp (G n)(g n)(r n3));
           msg
             (exp (G n)(exp (G n)(g n)(r n1)) (r n3));
           msg
             (exp (G n)(exp (G n)(g n)(r n2)) (r n3));
           msg (exp (G n)(g n)(r n5))]).
apply EQI_trans with (ml2:=  [msg (G n); msg (g n);
          msg (exp (G n)(g n)(r n1));
          msg (exp (G n)(g n)(r n2));
          msg (exp (G n)(g n)(r n4));
          msg (exp (G n)(g n)(r n3));
          msg (exp (G n)(exp (G n)(g n)(r n1)) (r n3));
          msg (exp (G n)(exp (G n)(g n)(r n2)) (r n3));
          msg (exp (G n)(g n)(r n5))]). apply line10.
symmetry. apply temp3. 
restr_swap_in 5 6 Final.
apply Final.
Qed.


