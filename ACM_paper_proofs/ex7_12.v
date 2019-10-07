(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                     Rohit Chadha <chadhar@missouri.edu>              *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)
Load "ex7_11".
(** This library presents a theorem that states,

[ Fresh(G,g,a,b,c,d) /\ (clos_bol b) -> [[ G;g;g^a;g^b;g^c; if_then_else_B b (g^ab) (g^bc)]] ~ [[G;g;g^a;g^b;g^c;g^d]] ]. *)

Variable fmb4 : message -> message -> message -> message ->  Bool.
Theorem Example20: forall (n n1 n2 n3 n4: nat), (Fresh [ n ; n1 ; n2 ; n3 ; n4] []  = true ) -> (clos_bol (fmb4  (g n)  (exp (G n) (g n) (r n1)) (exp (G n) (g n) (r n2)) (exp (G n) (g n) (r n3))) = true) -> [ msg (G n) ; msg (g n); msg (exp (G n) (g n) (r n1)); msg (exp (G n) (g n) (r n2)); msg (exp (G n) (g n) (r n3)); msg (if_then_else_M (fmb4  (g n) (exp (G n) (g n) (r n1)) (exp (G n) (g n) (r n2)) (exp (G n) (g n) (r n3))) (exp (G n) (exp (G n) (g n) (r n1)) (r n2))  (exp (G n) (exp (G n) (g n) (r n2)) (r n3)))] ~   [ msg (G n) ; msg (g n); msg (exp (G n) (g n) (r n1)); msg (exp (G n) (g n) (r n2)); msg (exp (G n) (g n) (r n3)); msg (exp (G n) (g n) (r n4))].

Proof. intros. 
assert(H2 : Fresh[n;n1;n2;n4] [] = true).
unfold Fresh in H.
apply andb_prop in H. inversion H.
unfold nodup_ilist in H1.
unfold count_occur in H1.
repeat rewrite <- beq_nat_refl in H1.
assert(H3: beq_nat n1 n = false).
Fr_pf.
assert(H4: beq_nat n2 n = false).
Fr_pf.
assert(H5: beq_nat n3 n =false).
Fr_pf.
assert(H6: beq_nat n4 n = false).
Fr_pf.
assert(H7: beq_nat n2 n1 = false).
Fr_pf.
assert(H8 : beq_nat n3 n1 = false).
Fr_pf.
assert(H9: beq_nat n4 n1 = false).
Fr_pf.
assert(H10: beq_nat n3 n2 = false).
Fr_pf.
assert(H11 : beq_nat n4 n2 = false).
Fr_pf.
assert(H12 : beq_nat n4 n3 = false).
Fr_pf.
(**************************************************************************************)
(*************************************************************************************)

unfold Fresh. unfold nodup_ilist. unfold count_occur. repeat rewrite <- beq_nat_refl.
 rewrite H3; rewrite H4;rewrite H6. simpl. rewrite H7;rewrite H9; rewrite H11.
simpl. reflexivity.
apply DDH in H2.
pose proof(FRESHIND).
assert (Frccl:  (clos_mylist ( [msg (G n); msg (g n);
        msg (exp (G n) (g n) (r n1));
        msg (exp (G n) (g n) (r n2));
        msg
          (exp (G n)
             (exp (G n) (g n) (r n1)) 
             (r n2))] ++ [msg (G n); msg (g n);
       msg (exp (G n) (g n) (r n1));
       msg (exp (G n) (g n) (r n2));
       msg (exp (G n) (g n) (r n4))])= true) /\ (Fresh [n3] ([msg (G n); msg (g n);
        msg (exp (G n) (g n) (r n1));
        msg (exp (G n) (g n) (r n2));
        msg
          (exp (G n)
             (exp (G n) (g n) (r n1)) 
             (r n2))] ++ [msg (G n); msg (g n);
       msg (exp (G n) (g n) (r n1));
       msg (exp (G n) (g n) (r n2));
       msg (exp (G n) (g n) (r n4))])= true) /\ (Fresh [n3]( [msg (G n); msg (g n);
        msg (exp (G n) (g n) (r n1));
        msg (exp (G n) (g n) (r n2));
        msg
          (exp (G n)
             (exp (G n) (g n) (r n1)) 
             (r n2))] ++ [msg (G n); msg (g n);
       msg (exp (G n) (g n) (r n1));
       msg (exp (G n) (g n) (r n2));
       msg (exp (G n) (g n) (r n4))])= true) /\ ( [msg (G n); msg (g n);
      msg (exp (G n) (g n) (r n1));
      msg (exp (G n) (g n) (r n2));
      msg
        (exp (G n)
           (exp (G n) (g n) (r n1)) (r n2))] ~
     [msg (G n); msg (g n);
     msg (exp (G n) (g n) (r n1));
     msg (exp (G n) (g n) (r n2));
     msg (exp (G n) (g n) (r n4))])).
repeat (split); repeat (reflexivity). 
simpl.
unfold Fresh in H.
apply andb_prop in H. inversion H.
unfold nodup_ilist in H3.
unfold count_occur in H3.
repeat rewrite <- beq_nat_refl in H3.
assert(H5: beq_nat n1 n = false).
Fr_pf.
assert(H6: beq_nat n2 n = false).
Fr_pf.
assert(H7: beq_nat n3 n =false).
Fr_pf.
assert(H8: beq_nat n4 n = false).
Fr_pf.
assert(H9: beq_nat n2 n1 = false).
Fr_pf.
assert(H10 : beq_nat n3 n1 = false).
Fr_pf.
assert(H11: beq_nat n4 n1 = false).

Fr_pf.
assert(H12: beq_nat n3 n2 = false).
Fr_pf.

assert(H13 : beq_nat n4 n2 = false).
Fr_pf.

assert(H14 : beq_nat n4 n3 = false).
Fr_pf.
(*******************************************************)

(*******************************************************)

SearchAbout beq_nat.
rewrite Nat.eqb_sym. rewrite H7. rewrite Nat.eqb_sym. rewrite H10.  rewrite Nat.eqb_sym. rewrite H12. rewrite H14. reflexivity. 


simpl.
unfold Fresh in H.
apply andb_prop in H. inversion H.
unfold nodup_ilist in H3.
unfold count_occur in H3.
repeat rewrite <- beq_nat_refl in H3.
assert(H5: beq_nat n1 n = false).
Fr_pf.
assert(H6: beq_nat n2 n = false).
Fr_pf.
assert(H7: beq_nat n3 n =false).
Fr_pf.
assert(H8: beq_nat n4 n = false).
Fr_pf.
assert(H9: beq_nat n2 n1 = false).
Fr_pf.
assert(H10 : beq_nat n3 n1 = false).
Fr_pf.
assert(H11: beq_nat n4 n1 = false).
Fr_pf.
assert(H12: beq_nat n3 n2 = false).
Fr_pf.

assert(H13 : beq_nat n4 n2 = false).
Fr_pf.

assert(H14 : beq_nat n4 n3 = false).
Fr_pf.

rewrite Nat.eqb_sym.
rewrite H7. rewrite Nat.eqb_sym. rewrite H10. rewrite Nat.eqb_sym. rewrite H12. rewrite H14.  simpl.
reflexivity. apply H2.
clear H1.

assert(H4: ((msg (r n3)) +++ [msg (G n); msg (g n);
        msg (exp (G n) (g n) (r n1));
        msg (exp (G n) (g n) (r n2));
        msg
          (exp (G n)
             (exp (G n) (g n) (r n1)) 
             (r n2))]) ~
       ( (msg (r n3)) +++ [msg (G n); msg (g n);
       msg (exp (G n) (g n) (r n1));
       msg (exp (G n) (g n) (r n2));
       msg (exp (G n) (g n) (r n4))])).

apply FRESHIND with (n1:=n3) (n2:=n3) in Frccl ; apply Frccl.

pose proof(FUNCApp_expatpos). 

simpl in H4.
apply FUNCApp_expatpos with (p1:= 2)(p2:= 3) (p3:= 1) in H4.
unfold exp_at_pos in H4.
simpl in H4.

restr_swap_in 6 7 H4.

apply FUNCApp_att4 with (p1:=3) (p2:=4) (p3:=5) (p4:= 6) (fmb4 := fmb4) in H4.
unfold getelt_at_pos in H4. simpl in H4. 
restr_swap_in 7 8 H4.


assert(DDHbc: Fresh[n;n2;n3;n4] [] = true).

clear H1.

unfold Fresh in H.
apply andb_prop in H. inversion H.
unfold nodup_ilist in H1.
unfold count_occur in H1.
repeat rewrite <- beq_nat_refl in H1.
assert(H5: beq_nat n1 n = false).
Fr_pf.
assert(H6: beq_nat n2 n = false).
Fr_pf.
assert(H7: beq_nat n3 n =false).
Fr_pf.
assert(H8: beq_nat n4 n = false).
Fr_pf.
assert(H9: beq_nat n2 n1 = false).
Fr_pf.
assert(H10 : beq_nat n3 n1 = false).
Fr_pf.
assert(H11: beq_nat n4 n1 = false).

Fr_pf.
assert(H12: beq_nat n3 n2 = false).
Fr_pf.

assert(H13 : beq_nat n4 n2 = false).
Fr_pf.


assert(H14 : beq_nat n4 n3 = false).
Fr_pf.
unfold Fresh. simpl. repeat rewrite <- beq_nat_refl.
rewrite Nat.eqb_sym.
rewrite H6.  rewrite Nat.eqb_sym. rewrite H7. rewrite H12. rewrite H8.  simpl. rewrite H13. simpl.
rewrite H14. simpl. 
reflexivity. 



apply DDH in DDHbc.
assert (Fracl:  (clos_mylist ( [msg (G n); msg (g n);
        msg (exp (G n) (g n) (r n2));
        msg (exp (G n) (g n) (r n3));
        msg
          (exp (G n)
             (exp (G n) (g n) (r n2)) 
             (r n3))] ++ [msg (G n); msg (g n);
       msg (exp (G n) (g n) (r n2));
       msg (exp (G n) (g n) (r n3));
       msg (exp (G n) (g n) (r n4))])= true) /\ (Fresh [n1] ([msg (G n); msg (g n);
        msg (exp (G n) (g n) (r n2));
        msg (exp (G n) (g n) (r n3));
        msg
          (exp (G n)
             (exp (G n) (g n) (r n2)) 
             (r n3))] ++ [msg (G n); msg (g n);
       msg (exp (G n) (g n) (r n2));
       msg (exp (G n) (g n) (r n3));
       msg (exp (G n) (g n) (r n4))])= true) /\ (Fresh [n1]( [msg (G n); msg (g n);
        msg (exp (G n) (g n) (r n2));
        msg (exp (G n) (g n) (r n3));
        msg
          (exp (G n)
             (exp (G n) (g n) (r n2)) 
             (r n3))] ++ [msg (G n); msg (g n);
       msg (exp (G n) (g n) (r n2));
       msg (exp (G n) (g n) (r n3));
       msg (exp (G n) (g n) (r n4))])= true) /\ ( [msg (G n); msg (g n);
      msg (exp (G n) (g n) (r n2));
      msg (exp (G n) (g n) (r n3));
      msg
        (exp (G n)
           (exp (G n) (g n) (r n2)) (r n3))] ~
     [msg (G n); msg (g n);
     msg (exp (G n) (g n) (r n2));
     msg (exp (G n) (g n) (r n3));
     msg (exp (G n) (g n) (r n4))])).
repeat (try split); repeat (try reflexivity). simpl. clear H1.
unfold Fresh in H.
apply andb_prop in H. inversion H.
unfold nodup_ilist in H1.
unfold count_occur in H1.
repeat rewrite <- beq_nat_refl in H1.
assert(H5: beq_nat n1 n = false).
Fr_pf.
assert(H6: beq_nat n2 n = false).
Fr_pf.
assert(H7: beq_nat n3 n =false).
Fr_pf.
assert(H8: beq_nat n4 n = false).
Fr_pf.
assert(H9: beq_nat n2 n1 = false).
Fr_pf.
assert(H10 : beq_nat n3 n1 = false).
Fr_pf.
assert(H11: beq_nat n4 n1 = false).
Fr_pf.
assert(H12: beq_nat n3 n2 = false).
Fr_pf.
assert(H13 : beq_nat n4 n2 = false).
Fr_pf.
assert(H14 : beq_nat n4 n3 = false).
Fr_pf.
unfold Fresh. simpl. repeat rewrite <- beq_nat_refl.
rewrite Nat.eqb_sym.
rewrite H5.   rewrite H9. rewrite H10. rewrite H11. 
reflexivity.  clear H1.
simpl.
unfold Fresh in H.
apply andb_prop in H. inversion H.
unfold nodup_ilist in H1.
unfold count_occur in H1.
repeat rewrite <- beq_nat_refl in H1.
assert(H5: beq_nat n1 n = false).
Fr_pf.
assert(H6: beq_nat n2 n = false).
Fr_pf.
assert(H7: beq_nat n3 n =false).
Fr_pf.
assert(H8: beq_nat n4 n = false).
Fr_pf.
assert(H9: beq_nat n2 n1 = false).
Fr_pf.
assert(H10 : beq_nat n3 n1 = false).
Fr_pf.
assert(H11: beq_nat n4 n1 = false).
Fr_pf.
assert(H12: beq_nat n3 n2 = false).
Fr_pf.
assert(H13 : beq_nat n4 n2 = false).
Fr_pf.
assert(H14 : beq_nat n4 n3 = false).
Fr_pf.
rewrite Nat.eqb_sym.
rewrite H5.   rewrite H9. rewrite H10. rewrite H11. 
reflexivity.  clear H1.
apply DDHbc.
assert(H6: ((msg (r n1)) +++ [msg (G n); msg (g n);
        msg (exp (G n) (g n) (r n2));
        msg (exp (G n) (g n) (r n3));
        msg
          (exp (G n)
             (exp (G n) (g n) (r n2)) 
             (r n3))]) ~
       ( (msg (r n1)) +++ [msg (G n); msg (g n);
       msg (exp (G n) (g n) (r n2));
       msg (exp (G n) (g n) (r n3));
       msg (exp (G n) (g n) (r n4))])).
apply FRESHIND with (n1:=n1) (n2:=n1) in Fracl; apply Fracl.
simpl in H6.
apply FUNCApp_expatpos with (p1:= 2)(p2:= 3) (p3:= 1) in H6.
unfold exp_at_pos in H6.
simpl in H6.
restr_swap_in 6 7 H6.
restr_swap_in 5 6 H6.
restr_swap_in 4 5 H6.
apply FUNCApp_att4 with (p1:=3) (p2:=4) (p3:=5) (p4:= 6) (fmb4:= fmb4) in H6.
unfold getelt_at_pos in H6. simpl in H6.
restr_swap_in 7 8 H6.
pose proof(IFBRANCH_M).
assert (ifbr: ([msg (G n); msg (g n); msg (exp (G n) (g n) (r n1));
 msg (exp (G n) (g n) (r n2));
 msg (exp (G n) (g n) (r n3))] ++[ bol
       (fmb4 (g n) (exp (G n) (g n) (r n1))
          (exp (G n) (g n) (r n2))
          (exp (G n) (g n) (r n3))); msg
   (if_then_else_M (fmb4 (g n) (exp (G n) (g n) (r n1))
         (exp (G n) (g n) (r n2))
         (exp (G n) (g n) (r n3)))
      (exp (G n) (exp (G n) (g n) (r n1)) (r n2))
      (exp (G n) (exp (G n) (g n) (r n2)) (r n3)))]) ~
([msg (G n); msg (g n); msg (exp (G n) (g n) (r n1));
msg (exp (G n) (g n) (r n2));
msg (exp (G n) (g n) (r n3))] ++
[bol (fmb4 (g n) (exp (G n) (g n) (r n1))
          (exp (G n) (g n) (r n2))
          (exp (G n) (g n) (r n3))); msg (if_then_else_M (fmb4 (g n) (exp (G n) (g n) (r n1))
         (exp (G n) (g n) (r n2))
         (exp (G n) (g n) (r n3)))
       (exp (G n) (g n) (r n4))
      (exp (G n) (g n) (r n4)))])).
apply IFBRANCH_M with (n:=5) (ml1:= [msg (G n); msg (g n); msg (exp (G n) (g n) (r n1));
 msg (exp (G n) (g n) (r n2));
 msg (exp (G n) (g n) (r n3))]) (ml2:= [msg (G n); msg (g n); msg (exp (G n) (g n) (r n1));
 msg (exp (G n) (g n) (r n2));
 msg (exp (G n) (g n) (r n3))])  (b:= (fmb4 (g n) (exp (G n) (g n) (r n1))
      (exp (G n) (g n) (r n2)) (exp (G n) (g n) (r n3)))) (b':= (fmb4 (g n) (exp (G n) (g n) (r n1))
      (exp (G n) (g n) (r n2)) (exp (G n) (g n) (r n3))))
 (x :=  (exp (G n) (exp (G n) (g n) (r n1)) (r n2))) (x':= (exp (G n) (g n) (r n4)))
(y:=  (exp (G n) (exp (G n) (g n) (r n2)) (r n3))) (y':= (exp (G n) (g n) (r n4))).
simpl. 
dropone_in H4. apply H4.
dropone_in H6. apply H6.
simpl in ifbr.
rewrite IFSAME_M with (b:= (fmb4 (g n) (exp (G n) (g n) (r n1))
            (exp (G n) (g n) (r n2))
            (exp (G n) (g n) (r n3)))) (x:=  (exp (G n) (g n) (r n4))) in ifbr.
restr_proj_in 6 ifbr.
apply ifbr.
Qed.



