(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                     Rohit Chadha <chadhar@missouri.edu>              *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)
Load "ex7_8".
(** This library defines a theorem that states, 
[[
For variables b1, b2, n1, n1', n2, n2', n3, n3', n4' : b1, b2, n1, n2, n3 ~ b1, b2, n1', n2, n3' ~ b1, b2, n4', n2', n3' -> 
if b1 then n1 else (if b2 then <n2, n3> else <n1, n2 ,n3> ~ if not(b2 ) then (if b1 then n1' else <n1' , n2' , n3'>)
else (if b1' then n4' else < n2' , n3' >).
]] 
*)

Theorem Example17: forall (n11  :nat) (n1  n2  n3 n1' n2' n3' n4' : nat),
[bol (Bvar n11) ; bol (Bvar (n11 + 1)); msg (N n1); msg (N n2); msg (N n3)] ~ [bol (Bvar n11) ; bol (Bvar (n11 + 1)); msg (N n1'); msg (N n2'); msg (N n3')] /\ [bol (Bvar n11); bol (Bvar (n11 + 1)); msg (N n1'); msg (N n2'); msg (N n3')] ~ [bol (Bvar n11) ; bol (Bvar (n11 + 1)); msg (N n4'); msg (N n2'); msg (N n3')] -> 
[msg (if_then_else_M (Bvar n11) (N n1) (if_then_else_M  (Bvar (n11 + 1))  (pair  (N n2)  (N n3))  (pair ( pair  (N n1)  (N n2)  ) (N n3) )))  ] ~ [msg ( if_then_else_M (notb (Bvar (n11 + 1))) (if_then_else_M (Bvar n11) (N n1')  (pair  (pair (N n1')  (N n2')) (N n3'))) (if_then_else_M (Bvar n11) (N n4')  (pair (N n2')  (N n3'))))].

Proof. intros.
assert(H1:  (if_then_else_M (Bvar n11) (N n1) (if_then_else_M (Bvar (n11 + 1))   (pair  (N n2)  (N n3))  (pair ( pair  (N n1)  (N n2)  ) (N n3) ))) # (if_then_else_M (Bvar (n11 + 1)) (if_then_else_M (Bvar n11) (N n1) (pair  (N n2)  (N n3)) ) (if_then_else_M (Bvar n11) (N n1) (pair ( pair  (N n1)  (N n2)  ) (N n3) )))).
rewrite IFMORPH_M4 with (n1 := n11)  (m1 := (N n1)).
reflexivity.
assert (H2: (if_then_else_M (Bvar (n11 + 1)) (if_then_else_M (Bvar n11) (N n1) (pair (N n2) (N n3)) )
          (if_then_else_M (Bvar n11) (N n1)  (pair (pair (N n1) (N n2)) (N n3)) )) # (if_then_else_M (notb (Bvar (n11 + 1)) ) (if_then_else_M (Bvar n11) (N n1)  (pair (pair (N n1) (N n2)) (N n3)))(if_then_else_M (Bvar n11)(N n1) (pair (N n2) (N n3)) ))).
rewrite    Example16_M . reflexivity.

assert (H3 : [ bol (notb (Bvar (n11 + 1))); msg (if_then_else_M (Bvar n11) (N n1)  (pair (pair (N n1) (N n2)) (N n3)) )] ~ [ bol (notb (Bvar (n11 + 1))); msg (if_then_else_M (Bvar n11) (N n1')  (pair (pair (N n1') (N n2')) (N n3')) )]).
inversion H.
apply FUNCApp_negpos with (p :=2) in H0.
 unfold neg_at_pos in H0 ;unfold chkbol_os in H0 ; unfold getelt_at_pos in H0.
  simpl in H0.     
apply FUNCApp_ifmnespair with (p1:=1) (p2:=3)(p3:=4) (p4:=5) in H0. unfold ifm_nespair in H0. unfold chkbol_os in H0. unfold getelt_at_pos in H0. unfold chkmsg_os in H0.  unfold pair_term_pos in H0. unfold pair_at_pos in H0. unfold getelt_at_pos in H0.  simpl in H0. 
(********drop first five elements**************************)
aply_in 5 dropone_in H0.
apply H0.
assert (H5: [ bol (notb (Bvar (n11 + 1))); msg (if_then_else_M (Bvar n11) (N n1)  (pair (N n2) (N n3)) )] ~ [ bol (notb (Bvar (n11 + 1))); msg (if_then_else_M (Bvar n11) (N n4')  (pair  (N n2') (N n3')) )]).
inversion H.
assert(H5: [bol (Bvar n11); bol (Bvar (n11 + 1)); msg (N n1); msg (N n2); msg (N n3)] ~[bol (Bvar n11); bol (Bvar (n11 + 1)); msg (N n4'); 
       msg (N n2'); msg (N n3')]).
apply EQI_trans with (ml1 := [bol (Bvar n11); bol (Bvar (n11 + 1)); msg (N n1); msg (N n2); msg (N n3)]) (ml2 := [bol (Bvar n11); bol (Bvar (n11 + 1)); msg (N n1'); msg (N n2'); msg (N n3')]) (ml3:=  [bol (Bvar n11); bol (Bvar (n11 + 1)); msg (N n4'); msg (N n2'); msg (N n3')]).
apply H0.
apply H4.
apply FUNCApp_negpos with (p :=2)  in H5.
 unfold neg_at_pos in H5 . unfold chkbol_os in H5.  simpl in H5.
apply FUNCApp_ifmpair with (p1:=1)(p2:=3)(p3:=4)(p4:=5) in H5. unfold ifm_pair in H5. unfold chkbol_os in H5. unfold getelt_at_pos in H5. unfold chkmsg_os in H5. unfold pair_at_pos in H5.  simpl in H5.

(***drop first five elements***********)
aply_in 5 dropone_in H5. 
apply H5.
assert (H6 : [bol (notb (Bvar (n11 + 1)));
      msg (if_then_else_M (Bvar n11) (N n1)  (pair  (pair (N n1) (N n2)) (N n3) ))] ~
     [bol (notb (Bvar (n11 + 1)));
     msg (if_then_else_M (Bvar n11) (N n1')   (pair  (pair (N n1') (N n2')) (N n3') ))] /\ [bol (notb (Bvar (n11 + 1)));
      msg (if_then_else_M (Bvar n11) (N n1)  (pair ( N n2) (N n3)))] ~
     [bol (notb (Bvar (n11 + 1)));
     msg (if_then_else_M (Bvar n11) (N n4')  (pair (N n2') (N n3')))]).
split.
apply H3. apply H5.
pose proof (IFBRANCH_M).
assert(H7 : [bol (notb (Bvar (n11 + 1))); msg (if_then_else_M (notb (Bvar (n11 + 1))) (if_then_else_M (Bvar n11) (N n1)   (pair  (pair (N n1) (N n2)) (N n3) )) (if_then_else_M (Bvar n11) (N n1)  (pair ( N n2) (N n3))))]~
[bol (notb (Bvar (n11 + 1))) ; msg (if_then_else_M (notb (Bvar (n11 + 1))) (if_then_else_M (Bvar n11) (N n1')   (pair  (pair (N n1') (N n2')) (N n3') )) (if_then_else_M (Bvar n11) (N n4')  (pair ( N n2') (N n3'))))]).
apply IFBRANCH_M with (ml1 := []) (ml2 := [])(b := (notb (Bvar (n11 + 1)))) (b' := (notb (Bvar (n11 + 1)))) (x := (if_then_else_M (Bvar n11) (N n1) (pair  (pair (N n1) (N n2)) (N n3) ))) (x' := (if_then_else_M (Bvar n11) (N n1') (pair  (pair (N n1') (N n2')) (N n3') ) ))  (y := (if_then_else_M (Bvar n11) (N n1)  (pair ( N n2) (N n3))))(y':=(if_then_else_M (Bvar n11) (N n4')  (pair (N n2') (N n3')))) . 
simpl. apply H3.
simpl. apply H5.
dropone_in H7.
rewrite Example16_M with (n:= (n11 + 1)) (m1 := (if_then_else_M (Bvar n11) (N n1)   (pair  (pair (N n1) (N n2)) (N n3) ))) in H7. 
rewrite <- IFMORPH_M4 with  (m1 := (N n1))  in H7.
apply H7. 
Qed.

