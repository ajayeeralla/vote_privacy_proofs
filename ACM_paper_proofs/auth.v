(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                     Rohit Chadha <chadhar@missouri.edu>              *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)
Load "dsaxioms".
Section dh_auth.
(** This library contains proof of the responder's authentication of the initior of authenticated version of the DH protocol (STS protocol). *)

(** # <b> Authenticated version of the DH protocol:</b>
</br>
Group description G and g are generated honestly, according to a randomized algorithm and are made public.
Public key, secret key pairs (pkA , skA ) and (pkB , skB ) are generated honestly for both A and B and pkA , pkB are made public.
<ul>
<li> The Initiator generates a random <i> a </i> in <i> Z<sub>|g|</sub> </i> and sends <i> g<sup>a</sup>. </li> 
<li> The Responder receives <i> g <sup> a </sup> </i>, generates a random <i> b </i> in <i> Z<sub>|g|</sub></i> and
sends <i> < g<sup>b</sup>, sign(skB, g<sup> b </sup>, g<sup>a</sup>) > </i>, and computes <i> (g <sup> a </sup>)<sup> b </sup> </i>. </li>
<li> The Initiator receives <i> < g<sup> b </sup> , sign(skB , g<sup> b</sup>, g<sup>a</sup> ) > </i>, verifies the signature, computes (g<sup> b </sup>)<sup> a </sup>, and sends <i> sign(skA , g <sup> a </sup>, g <sup>  b </sup> ) </i>.
<li> The Responder receives sign (skA, < g <sup> a </sup>, g <sup> b </sup> >), verifies the signature, and output <i> acc </i>. </li>
</ul>
#
 *)

(** Authentication is modeled as indistinguishability of two protocols, one in which the oracle reveals [TRue] if the given session is completed but no matching session (there exists an attack), and the one in which the oracle always reveals [FAlse]. *)

(** Protocol [Pi1] reveals [FAlse] always. *)

(** Frame [phi10] represents initial knowledge of the attacker. *)

Definition phi10 := [msg (G 0); msg (g 0); msg (pk (N 3)); msg (pk (N 4))].
Definition mphi10 := (conv_mylist_listm phi10).
Definition grn (n:nat) := (exp (G 0) (g 0) (r n)).
Definition x1 := (f mphi10).
Definition qa00 :=   (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) (grn 1) (if_then_else_M (EQ_M (to x1) (i 2)) (pair (grn 2) (sign (sk (N 4))  (pair (grn 2) x1))) O)).

(** Frame [phi11] represents attacker's knowledge during execution of the protocol. *)

Definition phi11 := phi10 ++ [msg qa00].
Definition mphi11 := (conv_mylist_listm phi11).
Definition x2 := (f mphi11). 
Definition qa10 :=  (if_then_else_M ((EQ_M (to x2) (i 1))& (ver (pk (N 4)) (pair (pi1 (x2))  (grn 1))   (pi2 (x2)))) (sign (sk (N 3)) (pair  (grn 1) (pi1 (x2))))  O ).
Definition qa01:=  (if_then_else_M (EQ_M (to x2) (i 2))& (ver (pk (N 3)) (pair (grn 1) (pi1 x2)) x2) acc O) .
Definition qa00_s :=  (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qa10 (if_then_else_M (EQ_M (to x1) (i 2)) qa01 O)).

(** Frame [phi12] also represents attackers's knowledge during execution of the protocol. *)

Definition phi12:= phi11 ++ [msg qa00_s].
Definition mphi12 := (conv_mylist_listm phi12).
Definition x3 := (f mphi12).
Definition qa20 :=  (if_then_else_M (EQ_M (reveal x3) (i 2))& (notb (EQ_M (pi1(x2)) (grn 1)) & (EQ_M x1 (grn 1)))  O O ).
Definition qa02 := (if_then_else_M (EQ_M (reveal x3) (i 2))& (notb ((EQ_M (pi1(x2)) (grn 1))) &  (EQ_M x1 (grn 1)))  O O ).
Definition qa10_s :=    (if_then_else_M ((EQ_M (to x2) (i 1))& (ver (pk (N 4)) (pair (pi1 (x2))  (grn 1)) (pi2 x2)))  qa20 O ).
Definition qa01_s := (if_then_else_M (EQ_M (to x2) (i 2))& (ver (pk (N 3)) (pair x1 (grn 1)) x2)& (EQ_M (pi1(x2)) (grn 1)) & (EQ_M x1 (grn 1)) qa02 O).
Definition qa00_ss :=  (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qa10_s (if_then_else_M (EQ_M (to x1) (i 2)) qa01_s O)).

(** Frame [phi13] attacker's knowledge at the end of the protocol. *)

Definition phi13 := phi12 ++ [msg qa00_ss].

(** Protocol Pi2 reveals [TRue] if there is an attack. 

 All the frames in this protocol are equal to the frames in Pi1 except the last one and we define it here. *)

Definition qb20 :=  (if_then_else_M (EQ_M (reveal x3) (i 2))& (notb (EQ_M (pi1(x2)) (grn 1)) & (EQ_M x1 (grn 1)))  O O ).

Definition qb02 := (if_then_else_M (EQ_M (reveal x3) (i 2))& (notb (EQ_M (pi1(x2)) (grn 1)) & (EQ_M x1 (grn 1))) new O ).

Definition qb10_s :=    (if_then_else_M ((EQ_M (to x2) (i 1))& (ver (pk (N 4)) (pair (pi1 (x2))  (grn 1)) (pi2 x2)))  qb20 O ).

Definition qb01_s := (if_then_else_M (EQ_M (to x2) (i 2))& (ver (pk (N 3)) (pair x1 (grn 1)) x2)& (EQ_M (pi1(x2)) (grn 1)) & (EQ_M x1 (grn 1)) qb02 O).

Definition qb00_ss :=  (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qb10_s (if_then_else_M (EQ_M (to x1) (i 2)) qb01_s O)).
Definition phi23 := phi12 ++ [msg qb00_ss].

(** Proof of [phi13 #### phi23], where [####] is an equivalence relations on mylists. *)

Theorem IND_DH_AUTH:   phi13 #### phi23.

Proof. unfold phi13, phi23, phi12, phi11, phi10. repeat unfold qa00, qa10 , qa01, qa20, qa02, qa10_s, qa01_s, qa00_s, qa00_ss.
simpl.
repeat unfold qb20, qb02, qb10_s, qb01_s, qb00_ss.
assert(trm3: (if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
         (if_then_else_M
            (EQ_M (to x2) (i 1)) & (ver (pk (N 4)) (pair (pi1 x2) (grn 1)) (pi2 x2))
            (if_then_else_M
               (EQ_M (reveal x3) (i 2)) &
               (notb (EQ_M (pi1 x2) (grn 1)) & (EQ_M x1 (grn 1))) O O) O)
         (if_then_else_M (EQ_M (to x1) (i 2))
            (if_then_else_M
               (((EQ_M (to x2) (i 2)) & (ver (pk (N 3)) (pair x1 (grn 1)) x2)) &
                (EQ_M (pi1 x2) (grn 1))) & (EQ_M x1 (grn 1))
               (if_then_else_M
                  (EQ_M (reveal x3) (i 2)) &
                  (notb (EQ_M (pi1 x2) (grn 1)) & (EQ_M x1 (grn 1))) O O) O) O)) # (if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
         (if_then_else_M
            (EQ_M (to x2) (i 1)) & (ver (pk (N 4)) (pair (pi1 x2) (grn 1)) (pi2 x2))
            (if_then_else_M
               (EQ_M (reveal x3) (i 2)) &
               (notb (EQ_M (pi1 x2) (grn 1)) & (EQ_M x1 (grn 1))) O O) O)
         (if_then_else_M (EQ_M (to x1) (i 2))
            (if_then_else_M
               (((EQ_M (to x2) (i 2)) & (ver (pk (N 3)) (pair x1 (grn 1)) x2)) &
                (EQ_M (pi1 x2) (grn 1))) & (EQ_M x1 (grn 1))
               (if_then_else_M
                  (EQ_M (reveal x3) (i 2)) &
                  (notb (EQ_M (pi1 x2) (grn 1)) & (EQ_M x1 (grn 1))) new O) O) O))).

assert(vef: (ver (pk (N 3)) (pair x1 (grn 1)) x2) ## FAlse).
pose proof(UFCMA 3 0 []  (pair x1 (grn 1)) x2).
simpl in H.
assert(H1: true = true /\ true = true  /\ true = true /\ 0 = 0).
repeat split. apply H in H1.
apply H1.
rewrite vef.
assert(pf:  (((EQ_M (to x2) (i 2)) & (FAlse)) & (EQ_M (pi1 x2) (grn 1))) &
            (EQ_M x1 (grn 1)) ## FAlse).
rewrite andB_FAlse_r with (b:= (EQ_M (to x2) (i 2))).
rewrite andB_FAlse_l with (b:= (EQ_M (pi1 x2) (grn 1))).
rewrite andB_FAlse_l with (b:= (EQ_M x1 (grn 1))). reflexivity.
rewrite pf.
repeat rewrite IFFALSE_M. reflexivity.  rewrite trm3. reflexivity. Qed.
End dh_auth.
