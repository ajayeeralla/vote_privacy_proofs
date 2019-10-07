(************************************************************************)
(* Copyright (c) 2017-2018, Ajay Kumar Eeralla <ae266@mail.missouri.edu>*)     
(************************************************************************)
 Require Export cpacca.
 Set Nested Proofs Allowed.
(** [Voting Phase] *)

(** STEP:3 *)
 
 Definition x3tt (n n':nat) := f (toListm (phi0 ++ [msg (tr 0 n 3  5 9), msg (tr 1 n' 4 6 10)])).

 Definition x3ftt (n n':nat) := f (toListm (phi0 ++ [msg (tr 1 n' 4 6 10), msg (tr 0 n 3 5 9)])).

 Definition acpt (n k r:nat) (x:message)  := (acc (c n k) pk (rb (N r)) x).
 Definition bk n := (rb (N n)).
 Definition se n := (re (N n)).


 Definition e n1 k n2 x ph n3 := (enc ((c n1 k), ((ub (c n1 k) pk (bk n2) x), ph)) (pke 2) (se n3)).

 Definition Avote x (n n':nat) k r ph n3 := (If ((to (x n n')) #? A) then (If (acpt n k r (x n n')) then (e n k r (x n n') ph n3) else O) else O).

 Definition Bvote x (n n':nat) k r ph n3 := (If ((to (x n n')) #? B) then (If (acpt n' k r (x n n')) then (e n' k r (x n n') ph n3) else O) else O).

 Definition t3 n n'   := If (theta x1 A) then (If (theta (x2t n) B) then (Avote x3tt n n' 3 5 TWO 11) else O) else (If (theta x1 B) then (If (theta (x2ft n') A) then (Bvote x3ftt n n' 4 6 TWO 11) else O) else O).

Definition phi3 n n' := (phi2 n n') ++ [msg (t3 n n')].

(** STEP:4 *)
 
Definition x4ttt (n n':nat) := f (toListm (phi0 ++ [msg (tr 0 n 3  5 9), msg (tr 1 n' 4 6 10), msg (e n 3 5 (x3tt n n') TWO 11) ])).
Definition x4fttt (n n': nat) := f (toListm (phi0 ++ [msg (tr 1 n' 4 6 10), msg (tr 0 n 3 5 9), msg (e n' 4 6 (x3tt n n') TWO 11) ])).

(***************)

 
Definition t4 n n' := If (theta x1 A) then
                         (If (theta (x2t n) B) then
                            (If ((to (x3tt n n')) #? A) then
                               (If (acpt n 3 5 (x3tt n n')) then
                                  (If ((to (x4ttt n n')) #? B) then
                                     (If (acpt n' 4 6 (x3tt n n')) then (e n' 4 6 (x3tt n n') TWO  12) else O) else O) else O) else O) else O) else (If (theta x1 B) then (If (theta (x2ft n') A) then (If ((to (x3ftt n n'))#?B) then (If (acpt n' 4 6 (x3ftt n n')) then (If ((to (x4fttt n n'))#? A) then (If (acpt n 3 5 (x3ftt n n')) then (e n 3 5 (x3ftt n n') TWO 12) else O) else O) else O) else O) else O) else O).
 
Definition phi4 n n' := (phi3 n n') ++ [msg (t4 n n')].

(** STEP:5 *)
Definition x5t (n n':nat) := f (toListm (phi0 ++ [msg (tr 0 n 3  5 9), msg (tr 1 n' 4 6 10), msg (e n 3 5 (x3tt n n') TWO 11), msg (e n' 4 6 (x3tt n n') TWO  12) ])).
Definition x5ft (n n':nat) := f (toListm (phi0 ++ [msg (tr 1 n' 4 6 10), msg (tr 0 n 3 5 9), msg (e n' 4 6 (x3ftt n n') TWO 11), msg (e n 3 5 (x3ftt n n') TWO 12) ])).

(****************)

Definition tau n (m:message) := match n, m with
                                | 1, m => (pi1 m) 
                                | 2, m => (pi1 (pi2 m))
                                | 3, m => (pi2 (pi2 m))
                                | _, _ => O
                                end.

Definition d n x := (dec (tau n x) (ske 2)).
Definition pchecks x ph := ((tau 3 (d 1 x)) #? ph) & ((tau 3 (d 2 x)) #? ph) & ((tau 3 (d 3 x)) #? ph).
Definition dist x y z := !(x #? y) & !(x#?z)& ! (y #? z). 
Definition isin (x y:message):Bool := (x #? (tau 1 y)) or (x #? (tau 2 y)) or (x #? (tau 3 y)).
Definition bcheck (x y:message):Bool := (isin x ((pi2 (tau 1 y)), ((pi2 (tau 2 y)), (pi2 (tau 3 y))))).

Definition label x y := If (x #? (pi2 (tau 1 y))) then (pi1 (tau 1 y))
                           else  (If (x#?(pi2 (tau 2 y))) then (pi1 (tau 2 y))
                                                       else (If (x #? (pi2 (tau 3 y))) then (pi1 (tau 3 y))
                                                            else O)).

Definition mchecks x (n n':nat) ph := (dist (d 1 (x n n')) (d 2 (x n n')) (d 3 (x n n'))) & (pchecks (x n n') ph).

Definition p n x := ( (tau 1 (d n x)), (tau 2 (d n x))).
 
Definition strm x := (shufl (p 1 x) (p 2 x) (p 3 x)).

Definition t5 x n n' := (If ((to (x n n'))#? M) then (If (mchecks x n n' TWO) then (strm (x n n')) else O) else O).

(***********************)

Definition t4s n n' := If (theta x1 A) then
                         (If (theta (x2t n) B) then
                            (If ((to (x3tt n n')) #? A) then
                               (If (acpt n 3 5 (x3tt n n')) then
                                  (If ((to (x4ttt n n')) #? B) then
                                     (If (acpt n' 4 6 (x3tt n n')) then (t5 x5t n n')
                                      else O)
                                   else O) else O) else O) else O)
                      else (If (theta x1 B) then
                              (If (theta (x2ft n') A) then
                                 (If ((to (x3ftt n n'))#?B) then
                                    (If (acpt n' 4 6 (x3ftt n n')) then
                                       (If ((to (x4fttt n n'))#? A) then
                                          (If (acpt n 3 5 (x3ftt n n')) then (t5 x5ft n n') else O) else O) else O) else O) else O) else O).

(****************************)
Definition phi5 n n' := (phi4 n n') ++ [msg (t4s n n')].


Axiom gen_prop1:  forall {n m} (n1 n2 n3 n4:nat) (t t0 t1: message) (z: mylist n) (z1:mylist m), let v0 := (V0 (f (toListm z))) in
                                                                                                      let v1 := (V1 (f (toListm z))) in
                                                                                                      (|v0|#?|v1|) ## TRue ->  (Fresh [n1; n2; n3; n4] (z++ z1++[msg t, msg t0, msg t1])  = true) ->  closMylist (z++[msg t]) = true -> ((length (distMvars [msg t0, msg t1]))=?  2)%nat = true -> bVarMylist [msg t0, msg t1] = nil  ->
    let mvl:= [5; 6] in  (mVarMsg t0) = mvl /\ (mVarMsg t1) = mvl ->
                 let r0 := (r n1) in
                 let r1 := (r n2) in
                 let k0 := (kc (N n3)) in
                 let k1 := (kc (N n4)) in
                 let c00 := (comm v0 k0) in
                 let c01 := (comm v0 k1) in
                 let c10 := (comm v1 k0) in
                 let c11 := (comm v1 k1) in
                 let t2 := ({{ 5 := (bl c00 t r0) }} ({{ 6:=(bl c11 t r1) }} t0)) in
                 let t3 := ({{ 5 := (bl c00 t r0) }} ({{ 6:=(bl c11 t r1) }} t1)) in
                 let t4 := ({{ 5 := (bl c10 t r0) }} ({{ 6:=(bl c01 t r1) }} t0)) in
                 let t5 := ({{ 5 := (bl c10 t r0) }} ({{ 6:=(bl c01 t r1) }} t1)) in
                 let lt1 := (((ub c00 t r0 t2), (c00, k0)), ((ub c11 t r1 t2), (c11, k1)) ) in
                 let lt2 := ((ub c00 t r0 t2), (c00, |_)) in
                 let lt3 := (|_, ((ub c11 t r1 t3), c11)) in
                 let rt1 := (((ub c10 t r1 t5), (c10, k0)), ((ub c01 t r0 t4), (c01, k1))) in
                 let rt2 := ((ub c10 t r0 t4), (c10, |_)) in 
                 let rt3 := (|_, ((ub c01 t r1 t5), c01)) in
                
                 
                 (z++z1++[msg (bl c00 t r0), msg (bl c11 t r1),
                        msg (If (acc c00 t r0 t2)& (acc c11 t r1 t3) then lt1 else (If (acc c00 t r0 t2) then lt2 else (If (acc c11 t r1 t3) then lt3  else (|_, |_))))])
                    ~
                   
                    (z++z1++[msg (bl c10 t r0), msg (bl c01 t r1),
                             msg (If (acc c10 t r0 t4)& (acc c01 t r1 t5) then rt1 else (If (acc c10 t r0 t4)  then rt2 else (If (acc c01 t r1 t5) then rt3 else (|_, |_))))]).



Axiom gen_prop3:  forall {n m} (n1 n2 n3 n4:nat) (t t0 t1: message) (z: mylist n) (z1:mylist m), let v0 := (V0 (f (toListm z))) in
                                                                                                      let v1 := (V1 (f (toListm z))) in
                                                                                                      (|v0|#?|v1|) ## TRue ->  (Fresh [n1; n2; n3; n4] (z++ z1++[msg t, msg t0, msg t1])  = true) ->  closMylist (z++[msg t]) = true -> ((length (distMvars [msg t0, msg t1]))=?  2)%nat = true -> bVarMylist [msg t0, msg t1] = nil  ->
    let mvl:= [5; 6] in  (distMvars [msg t0]) = mvl /\ (distMvars [msg t1]) = mvl ->
                 let r0 := (r n1) in
                 let r1 := (r n2) in
                 let k0 := (kc (N n3)) in
                 let k1 := (kc (N n4)) in
                 let c00 := (comm v0 k0) in
                 let c01 := (comm v0 k1) in
                 let c10 := (comm v1 k0) in
                 let c11 := (comm v1 k1) in
                 let t2 := ({{ 5 := (bl c00 t r0) }} ({{ 6:=(bl c11 t r1) }} t0)) in
                 let t3 := ({{ 5 := (bl c00 t r0) }} ({{ 6:=(bl c11 t r1) }} t1)) in
                 let t4 := ({{ 5 := (bl c10 t r0) }} ({{ 6:=(bl c01 t r1) }} t0)) in
                 let t5 := ({{ 5 := (bl c10 t r0) }} ({{ 6:=(bl c01 t r1) }} t1)) in
                 let lt1 := (((ub c00 t r0 t2), (c00, k0)), ((ub c11 t r1 t2), (c11, k1)) ) in
                 let lt2 := ((ub c00 t r0 t2), (c00, |_)) in
                 let lt3 := (|_, ((ub c11 t r1 t3), c11)) in
                 let rt1 := (((ub c10 t r1 t5), (c10, k0)), ((ub c01 t r0 t4), (c01, k1))) in
                 let rt2 := ((ub c10 t r0 t4), (c10, |_)) in 
                 let rt3 := (|_, ((ub c01 t r1 t5), c01)) in
                
                 
                 (z++z1++[msg (bl c00 t r0), msg (bl c11 t r1), bol (acc c00 t r0 t2)& (acc c11 t r1 t3), bol (acc c00 t r0 t2), bol (acc c11 t r1 t3), msg lt3])
                      
                    ~
                   
                    (z++z1++[msg (bl c10 t r0), msg (bl c01 t r1), bol (acc c10 t r0 t4)& (acc c01 t r1 t5), bol (acc c10 t r0 t4), bol (acc c01 t r1 t5), msg rt3]).
(** This is actually, Ex 7.4 in the other paper *)
Axiom symEql: forall x y, (|x|#?|y|) ## (|y|#?|x|).
Axiom refEql: forall x, (|x|#?|x|) ## TRue.
Axiom zeroEql1: forall x y, (|x|#?|y|) ## TRue -> (|x| #? |(z y)|) ## TRue.
Axiom len_reg: forall x1 y1 x2 y2, (|x1|#?|y1|) ## TRue -> (|x2|#?|y2|) ## TRue -> (|(x1, x2)| #? |(y1, y2)|) ## TRue.
Axiom len_prev_comp: forall (x:nat -> nat -> message) n n', (|(x n n')| #? |(x n' n)|) ## TRue.

Axiom ubEql: forall x1 y1 x2 y2 x3 y3 x4 y4, (|x1|#?|y1|) ## TRue -> (|x2|#?|y2|) ## TRue -> (|x3|#?|y3|) ## TRue -> (|x4|#?|y4|) ## TRue ->  (| (ub x1 x2 x3 x4)| #? | (ub y1 y2 y3 y4)|) ## TRue.
Axiom voteEql: forall {x}, (^? x) = true -> (|(V0 x)| #? |(V1 x)|)## TRue. 
 
Axiom tempax: forall  t n n' n'' u v, (dec t (ske n)) # (If (t#? {u}_n^^n') then u else (If (t#?{v}_n^^n'') then v else (dec t (ske n)))).

(** morphism for tau *)
Axiom tau_cong: forall n1 n2 m1 m2, n1 = n2 -> m1 # m2 -> tau n1 m1 # tau n2 m2.
Add Parametric Morphism: (@tau) with
signature eq ==> EQm ==> EQm as tau_mor.
Proof. intros.
apply tau_cong;try auto.
Qed.
(*
Theorem frame5ind: (phi5 0 1) ~ (phi5 1 0).
Proof.
unfold phi5, phi4, phi3, phi2, phi1.
unfold t1, t2, t3, t4, t4s.
unfold t5, mchecks, strm, p, d.
unfold pchecks. simpl.
apply IFBRANCH_M5 with (ml1:= phi0) (ml2:= phi0).
simpl. unfold Avote. 
apply IFBRANCH_M4 with (ml1:= (phi0 ++ [bol (theta x1 A), msg (tr 0 0 3 5 9)]))(ml2:= (phi0 ++ [bol (theta x1 A), msg (tr 0 1 3 5 9)])). 
apply IFBRANCH_M3 with (ml1:= (phi0 ++ [bol (theta x1 A), msg (tr 0 0 3 5 9), bol (theta (x2t 0) B), msg (tr 1 1 4 6 10)]))(ml2:= (phi0 ++ [bol (theta x1 A), msg (tr 0 1 3 5 9), bol (theta (x2t 1) B), msg (tr 1 0 4 6 10)])).

 
apply IFBRANCH_M3 with (ml1:= (phi0 ++ [bol (theta x1 A), msg (tr 0 0 3 5 9), bol (theta (x2t 0) B), msg (tr 1 1 4 6 10), bol (to (x3tt 0 1)) #? A]))(ml2:= (phi0 ++ [bol (theta x1 A), msg (tr 0 1 3 5 9), bol (theta (x2t 1) B), msg (tr 1 0 4 6 10), bol (to (x3tt 1 0)) #? A])).
 
apply IFBRANCH_M2 with (ml1:= (phi0 ++ [bol (theta x1 A), msg (tr 0 0 3 5 9), bol (theta (x2t 0) B), msg (tr 1 1 4 6 10), bol (to (x3tt 0 1)) #? A, bol (acpt 0 3 5 (x3tt 0 1)), msg (e 0 3 5 (x3tt 0 1) TWO 11)]))(ml2:= (phi0 ++ [bol (theta x1 A), msg (tr 0 1 3 5 9), bol (theta (x2t 1) B), msg (tr 1 0 4 6 10), bol (to (x3tt 1 0)) #? A, bol (acpt 1 3 5 (x3tt 1 0)), msg (e 1 3 5 (x3tt 1 0) TWO 11)])).
 
apply IFBRANCH_M2 with (ml1:= (phi0 ++ [bol (theta x1 A), msg (tr 0 0 3 5 9), bol (theta (x2t 0) B), msg (tr 1 1 4 6 10), bol (to (x3tt 0 1)) #? A, bol (acpt 0 3 5 (x3tt 0 1)), msg (e 0 3 5 (x3tt 0 1) TWO 11), bol (to (x4ttt 0 1)) #? B]))(ml2:= (phi0 ++ [bol (theta x1 A), msg (tr 0 1 3 5 9), bol (theta (x2t 1) B), msg (tr 1 0 4 6 10), bol (to (x3tt 1 0)) #? A, bol (acpt 1 3 5 (x3tt 1 0)), msg (e 1 3 5 (x3tt 1 0) TWO 11), bol (to (x4ttt 1 0)) #? B])).
 
apply IFBRANCH_M1 with (ml1:= (phi0 ++ [bol (theta x1 A), msg (tr 0 0 3 5 9), bol (theta (x2t 0) B), msg (tr 1 1 4 6 10), bol (to (x3tt 0 1)) #? A, bol (acpt 0 3 5 (x3tt 0 1)), msg (e 0 3 5 (x3tt 0 1) TWO 11), bol (to (x4ttt 0 1)) #? B, bol (acpt 1 4 6 (x3tt 0 1)), msg (e 1 4 6 (x3tt 0 1) TWO 12)]))(ml2:= (phi0 ++ [bol (theta x1 A), msg (tr 0 1 3 5 9), bol (theta (x2t 1) B), msg (tr 1 0 4 6 10), bol (to (x3tt 1 0)) #? A, bol (acpt 1 3 5 (x3tt 1 0)), msg (e 1 3 5 (x3tt 1 0) TWO 11), bol (to (x4ttt 1 0)) #? B, bol (acpt 0 4 6 (x3tt 1 0)), msg (e 0 4 6 (x3tt 1 0) TWO 12)])). 

simpl. unfold d. unfold dist.

pose proof(tempax (tau 1 (x5t 0 1)) 2 11 12 (c 0 3, (ub (c 0 3) pk (bk 5) (x3tt 0 1), TWO)) (c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO))).
pose proof(tempax  (tau 2 (x5t 0 1)) 2 11 12 (c 0 3, (ub (c 0 3) pk (bk 5) (x3tt 0 1), TWO)) (c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO))).
pose proof(tempax  (tau 3 (x5t 0 1)) 2 11 12 (c 0 3, (ub (c 0 3) pk (bk 5) (x3tt 0 1), TWO)) (c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO))).


pose proof(tempax  (tau 1 (x5t 1 0)) 2 11 12 (c 1 3, (ub (c 1 3) pk (bk 5) (x3tt 1 0), TWO)) (c 0 4, (ub (c 0 4) pk (bk 6) (x3tt 1 0), TWO))).
pose proof(tempax  (tau 2 (x5t 1 0)) 2 11 12 (c 1 3, (ub (c 1 3) pk (bk 5) (x3tt 1 0), TWO)) (c 0 4, (ub (c 0 4) pk (bk 6) (x3tt 1 0), TWO))).
pose proof(tempax  (tau 3 (x5t 1 0)) 2 11 12 (c 1 3, (ub (c 1 3) pk (bk 5) (x3tt 1 0), TWO)) (c 0 4, (ub (c 0 4) pk (bk 6) (x3tt 1 0), TWO))).
rewrite H, H0, H1, H2, H3, H4.
clear. simpl.



rewrite tempax.
apply IFBRANCH_M1 with (ml1:= (phi0 ++ [bol (theta x1 A), msg (tr 0 0 3 5 9), bol (theta (x2t 0) B), msg (tr 1 1 4 6 10), bol (to (x3tt 0 1)) #? A, bol (acpt 0 3 5 (x3tt 0 1)), msg (e 0 3 5 (x3tt 0 1) TWO 11), bol (to (x4ttt 0 1)) #? B, bol (acpt 1 4 6 (x3tt 0 1)), msg (e 1 4 6 (x3tt 0 1) TWO 12), bol (to (x5t 0 1)) #? M]))(ml2:= (phi0 ++ [bol (theta x1 A), msg (tr 0 1 3 5 9), bol (theta (x2t 1) B), msg (tr 1 0 4 6 10), bol (to (x3tt 1 0)) #? A, bol (acpt 1 3 5 (x3tt 1 0)), msg (e 1 3 5 (x3tt 1 0) TWO 11), bol (to (x4ttt 1 0)) #? B, bol (acpt 0 4 6 (x3tt 1 0)), msg (e 0 4 6 (x3tt 1 0) TWO 12), bol (to (x5t 1 0)) #? M])).

simpl.


unfold theta, tr, e.
rewrite tempax. *)

Theorem frame4goal1: [msg A, msg B, msg M, msg C1, msg C2, msg C3, msg ONE, msg TWO, msg THREE, msg (vk 0), msg (vk 1), msg (pke 2), 
   bol (theta x1 A), msg (tr 0 0 3 5 9), bol (theta (x2t 0) B), msg (tr 1 1 4 6 10), bol (to (x3tt 0 1)) #? A,
   bol (acpt 0 3 5 (x3tt 0 1)), msg {(c 0 3, (ub (c 0 3) pk (bk 5) (x3tt 0 1), TWO)) }_ 2 ^^ 11, 
   bol (to (x4ttt 0 1)) #? B, bol (acpt 1 4 6 (x3tt 0 1)), msg {(c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO)) }_ 2 ^^ 12] ~
  [msg A, msg B, msg M, msg C1, msg C2, msg C3, msg ONE, msg TWO, msg THREE, msg (vk 0), msg (vk 1), msg (pke 2), 
  bol (theta x1 A), msg (tr 0 1 3 5 9), bol (theta (x2t 1) B), msg (tr 1 0 4 6 10), bol (to (x3tt 1 0)) #? A,
  bol (acpt 1 3 5 (x3tt 1 0)), msg {(c 1 3, (ub (c 1 3) pk (bk 5) (x3tt 1 0), TWO)) }_ 2 ^^ 11, 
  bol (to (x4ttt 1 0)) #? B, bol (acpt 0 4 6 (x3tt 1 0)), msg {(c 0 4, (ub (c 0 4) pk (bk 6) (x3tt 1 0), TWO)) }_ 2 ^^  12].
   Proof.

(** l1 ++ [e1] ++ [e2] ~ l2 ++ [e1'] ++ [e2'] *)

(** Now, using ENCCCA2, we prove that, l1 ++ [e1] ++ [e2] ~ l1 ++ [z(e1)] ++ [z(e2)]  **) 

     
pose proof(EXTENCCCA2 (tau 1 (x5t 0 1)) (c 0 3, (ub (c 0 3) pk (bk 5) (x3tt 0 1), TWO)) (z (c 0 3, (ub (c 0 3) pk (bk 5) (x3tt 0 1), TWO))) O (c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO)) (z (c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO))) O 0 1 2 11 12 13 14 ([msg A, msg B, msg M, msg C1, msg C2, msg C3, msg ONE, msg TWO, msg THREE, msg (vk 0), msg (vk 1), msg (pke 2), 
   msg (tr 0 0 3 5 9), msg (tr 1 1 4 6 10), bol (to (x3tt 0 1)) #? A, bol (acpt 0 3 5 (x3tt 0 1)), bol (acpt 1 4 6 (x3tt 0 1)), msg (Mvar 0), msg (Mvar 1)])).
 simpl in H.  
do 2  rewrite zeroEql1 in H; try rewrite refEql.
simpl.  do 4 rewrite IFTRUE_M in H. simpl. 


(** Assuming the proposition1 with z= sublist(l1) ++ [z(e1)] ++ [z(e2)] and again using ENCCCA2, we get that
 l1 ++ [z(e1)] ++ [z(e2)] ~ l2 ++ [e1'] ++ [e2'] *)
(** 3nd Branch *)


 
Eval compute in (x3tt 0 1). 
Definition x3ttx := f (toListm (phi0 ++ [msg ((vk 0), (Mvar 5, (sign (Mvar 5) (ssk 0) (rs (N 9)))))] ++ [msg ((vk 1), (Mvar 6, (sign (Mvar 6) (ssk 1) (rs (N 10)))))])).

Definition sr (n:nat) := (rs (N n)).


pose proof (gen_prop3 5 6 3 4 (pubkey x1) (x3ttx) (x3ttx) phi0 [msg {(z (c 0 3, (ub (c 0 3) pk (bk 5) (x3tt 0 1), TWO)))}_ 2 ^^ 13,  msg {z (c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO)) }_ 2 ^^ 14, msg (ssk 0), msg (ssk 1), msg (sr 9), msg (sr 10) ]). unfold distMvars in H0.
 simpl in H0.
 unfold Fresh in H0. simpl in H0.
 rewrite voteEql in H0. 
restr_proj_in 21 H0; simpl; try split; try reflexivity.
Ltac dropLast_in H1 :=
  match goal with
  | [H: ?L1~?L2 |- _] => match H with
                           | H1 =>  restr_proj_in (length (toListm L1)) H
                         end
                           end.
dropLast_in H0.

 

Ltac signTerm n n' k r a r' H := funapptrmhypbl (msg (s n k r a r')) (msg (s n' k r a r')) H;
                                 funapptrmhypbl (msg (tr a n k r r')) (msg (tr a n' k r r')) H; simpl; try reflexivity.
                               

 signTerm 0 1 3 5 0 9 H0.
 signTerm 1 0 4 6 1 10 H0. 

Ltac toTerm x n n' a H := funapptrmhypbl (msg (x n n')) (msg (x n' n)) H;
                          funapptrmhypbl (msg (to (x n n'))) (msg (to (x n' n))) H;
                          funapptrmhypbl (bol ((to (x n n')) #? a))  (bol ((to (x n' n)) #? a)) H; simpl; try reflexivity.
 

funapptrmhypbl (msg (x3tt 0 1)) (msg (x3tt 1 0)) H0; simpl; try reflexivity.
funapptrmhypbl (msg (to (x3tt 0 1))) (msg (to (x3tt 1 0))) H0; simpl; try reflexivity.
funapptrmhypbl (bol ((to (x3tt 0 1)) #? A))  (bol ((to (x3tt 1 0)) #? A)) H0; simpl; try reflexivity.


do 6 (restr_proj_in 15 H0).
restr_proj_in 17 H0 . restr_proj_in 18 H0. do 2 restr_proj_in 19 H0.
Eval compute in (x3tt 0 1). 
 repeat unfold tr, acpt, vk, b, c, s. 
restr_swap_in 13 17 H0.
restr_swap_in 14 18 H0.
restr_swap_in 15 19 H0.  
restr_swap_in 18 19 H0.
restr_swap_in 17 18 H0.
restr_swap_in 16 17 H0. 



assert ( [msg A, msg B, msg M, msg C1, msg C2, msg C3, msg ONE, msg TWO, msg THREE, msg (pi1 (ks (N 0))), msg (pi1 (ks (N 1))), msg (pi1 (ke (N 2))),
       msg
         (pi1 (ks (N 0)),
         (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
            (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 5)),
         sign
           (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
              (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 5))) (pi2 (ks (N 0))) 
           (rs (N 9)))),
       msg
         (pi1 (ks (N 1)),
         (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
            (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6)),
         sign
           (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
              (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6))) (pi2 (ks (N 1))) 
           (rs (N 10)))),
       bol
         (to
            (f
               [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
               (pi1 (ks (N 0)),
               (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                  (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 5)),
               sign
                 (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                    (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 5))) (pi2 (ks (N 0))) 
                 (rs (N 9))));
               (pi1 (ks (N 1)),
               (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                  (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6)),
               sign
                 (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                    (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6))) (pi2 (ks (N 1))) 
                 (rs (N 10))))])) #? A, bol (acpt 0 3 5 (x3tt 0 1)), bol (acpt 1 4 6 (x3tt 0 1)),
       msg
         {(comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)),
          (ub (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
             (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 5))
             (f
                [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
                (pi1 (ks (N 0)),
                (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                   (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 5)),
                sign
                  (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                     (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 5))) (pi2 (ks (N 0))) 
                  (rs (N 9))));
                (pi1 (ks (N 1)),
                (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                   (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6)),
                sign
                  (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                     (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6))) (pi2 (ks (N 1))) 
                  (rs (N 10))))]), TWO)) }_ 2 ^^ 11, msg {(c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO)) }_ 2 ^^ 12] ~ [msg A, msg B, msg M, msg C1, msg C2, msg C3, msg ONE, msg TWO, msg THREE, msg (vk 0), msg (vk 1), msg (pke 2), msg (tr 0 1 3 5 9), 
       msg (tr 1 0 4 6 10), bol (to (x3tt 1 0)) #? A, bol (acpt 1 3 5 (x3tt 1 0)), bol (acpt 0 4 6 (x3tt 1 0)),
       msg {z (c 0 3, (ub (c 0 3) pk (bk 5) (x3tt 0 1), TWO)) }_ 2 ^^ 13, msg {z (c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO)) }_ 2 ^^ 14]).

apply EQI_trans with (ml2:= [msg A, msg B, msg M, msg C1, msg C2, msg C3, msg ONE, msg TWO, msg THREE, msg (vk 0), msg (vk 1), msg (pke 2), msg (tr 0 0 3 5 9), 
        msg (tr 1 1 4 6 10), bol (to (x3tt 0 1)) #? A, bol (acpt 0 3 5 (x3tt 0 1)), bol (acpt 1 4 6 (x3tt 0 1)),
        msg {z (c 0 3, (ub (c 0 3) pk (bk 5) (x3tt 0 1), TWO)) }_ 2 ^^ 13, msg {z (c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO)) }_ 2 ^^ 14]). 
apply H; repeat try split; try reflexivity.
assumption. clear H H0.
 
(** inorder to apply ENCCCA2 axiom, I do need utilize the axioms such as [CommEql], |V0x| = |V1x| and so on *)

 
pose proof(EXTENCCCA2 (tau 1 (x5t 0 1)) (z (c 0 3, (ub (c 0 3) pk (bk 5) (x3tt 0 1), TWO))) (c 1 3, (ub (c 1 3) pk (bk 5) (x3tt 1 0), TWO)) O (z (c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO))) (c 0 4, (ub (c 0 4) pk (bk 6) (x3tt 1 0), TWO)) O 0 1 2 13 14 11 12 [msg A, msg B, msg M, msg C1, msg C2, msg C3, msg ONE, msg TWO, msg THREE, msg (vk 0), msg (vk 1), msg (pke 2), msg (tr 0 1 3 5 9), 
       msg (tr 1 0 4 6 10), bol (to (x3tt 1 0)) #? A, bol (acpt 1 3 5 (x3tt 1 0)), bol (acpt 0 4 6 (x3tt 1 0)),
       msg (Mvar 0), msg (Mvar 1)]).
simpl in H.

(** I will come back to here later *)

(** This is not true in general, I'll come back it later *)

 


Check x3tt.

assert( (| z (c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO)) |) #? (| (c 0 4, (ub (c 0 4) pk (bk 6) (x3tt 1 0), TWO)) |) ## TRue).
rewrite symEql.
apply zeroEql1. apply len_reg. 

   
pose proof (commEql 4 4 (V1 x1) (V0 x1)). 
rewrite symEql in H0. rewrite voteEql in H0. rewrite IFTRUE_B in H0.
rewrite symEql.
apply H0.

try split; try reflexivity. unfold Fresh. simpl. reflexivity.
simpl.
reflexivity.
apply len_reg.


apply ubEql.

pose proof (commEql 4 4 (V1 x1) (V0 x1)).
rewrite symEql in H0. rewrite voteEql in H0. rewrite IFTRUE_B in H0.
rewrite symEql.
apply H0.

try split; try reflexivity. unfold Fresh. simpl. reflexivity.
simpl.
reflexivity.
 apply refEql.
apply refEql.
apply len_prev_comp.
apply refEql.
rewrite H0 in H.

assert ( (|z (c 0 3, (ub (c 0 3) pk (bk 5) (x3tt 0 1), TWO))|#? |(c 1 3, (ub (c 1 3) pk (bk 5) (x3tt 1 0), TWO))|) ## TRue).

rewrite symEql. 
apply zeroEql1. apply len_reg. 
    
pose proof (commEql 3 3 (V1 x1) (V0 x1)).
rewrite symEql in H2. rewrite voteEql in H2. rewrite IFTRUE_B in H2.
apply H2.

try split; try reflexivity. unfold Fresh. simpl. reflexivity.
simpl.
reflexivity.
apply len_reg.
apply ubEql.

pose proof (commEql 3 3 (V1 x1) (V0 x1)).
rewrite symEql in H2. rewrite voteEql in H2. rewrite IFTRUE_B in H2.
apply H2.

try split; try reflexivity. unfold Fresh. simpl. reflexivity.
simpl.
reflexivity.
apply refEql. apply refEql.
apply len_prev_comp.
apply refEql.
rewrite H2 in H.
clear H0 H2.

repeat rewrite IFTRUE_M in H.  

(** transitivity *)


assert ( [msg A, msg B, msg M, msg C1, msg C2, msg C3, msg ONE, msg TWO, msg THREE, msg (pi1 (ks (N 0))), 
        msg (pi1 (ks (N 1))), msg (pi1 (ke (N 2))),
        msg
          (pi1 (ks (N 0)),
          (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
             (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
             (rb (N 5)),
          sign
            (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
               (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
               (rb (N 5))) (pi2 (ks (N 0))) (rs (N 9)))),
        msg
          (pi1 (ks (N 1)),
          (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
             (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
             (rb (N 6)),
          sign
            (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
               (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
               (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10)))),
        bol
          (to
             (f
                [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
                (pi1 (ks (N 0)),
                (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                   (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
                   (rb (N 5)),
                sign
                  (bl
                     (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                     (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
                     (rb (N 5))) (pi2 (ks (N 0))) (rs (N 9))));
                (pi1 (ks (N 1)),
                (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                   (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
                   (rb (N 6)),
                sign
                  (bl
                     (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                     (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
                     (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))])) #? A, bol (acpt 0 3 5 (x3tt 0 1)), bol (acpt 1 4 6 (x3tt 0 1)),
        msg
          {(comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)),
           (ub (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
              (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
              (rb (N 5))
              (f
                 [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
                 (pi1 (ks (N 0)),
                 (bl
                    (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                    (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
                    (rb (N 5)),
                 sign
                   (bl
                      (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                         (kc (N 3)))
                      (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
                      (rb (N 5))) (pi2 (ks (N 0))) (rs (N 9))));
                 (pi1 (ks (N 1)),
                 (bl
                    (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                    (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
                    (rb (N 6)),
                 sign
                   (bl
                      (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                         (kc (N 4)))
                      (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
                      (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))]), TWO)) }_ 2 ^^ 11,
        msg {(c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO)) }_ 2 ^^ 12] ~  [msg A, msg B, msg M, msg C1, msg C2, msg C3, msg ONE, msg TWO, msg THREE, msg (pi1 (ks (N 0))), msg (pi1 (ks (N 1))),
      msg (pi1 (ke (N 2))),
      msg
        (pi1 (ks (N 0)),
        (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
           (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
           (rb (N 5)),
        sign
          (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
             (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
             (rb (N 5))) (pi2 (ks (N 0))) (rs (N 9)))),
      msg
        (pi1 (ks (N 1)),
        (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
           (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
           (rb (N 6)),
        sign
          (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
             (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
             (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10)))),
      bol
        (to
           (f
              [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
              (pi1 (ks (N 0)),
              (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                 (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
                 (rb (N 5)),
              sign
                (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                   (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
                   (rb (N 5))) (pi2 (ks (N 0))) (rs (N 9))));
              (pi1 (ks (N 1)),
              (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                 (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
                 (rb (N 6)),
              sign
                (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                   (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
                   (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))])) #? A,
      bol
        (acc (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
           (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
           (rb (N 5))
           (f
              [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
              (pi1 (ks (N 0)),
              (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                 (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
                 (rb (N 5)),
              sign
                (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                   (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
                   (rb (N 5))) (pi2 (ks (N 0))) (rs (N 9))));
              (pi1 (ks (N 1)),
              (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                 (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
                 (rb (N 6)),
              sign
                (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                   (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
                   (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))])),
      bol
        (acc (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
           (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
           (rb (N 6))
           (f
              [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
              (pi1 (ks (N 0)),
              (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                 (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
                 (rb (N 5)),
              sign
                (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                   (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
                   (rb (N 5))) (pi2 (ks (N 0))) (rs (N 9))));
              (pi1 (ks (N 1)),
              (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                 (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
                 (rb (N 6)),
              sign
                (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                   (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
                   (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))])),
      msg
        {(comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)),
         (ub (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
            (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
            (rb (N 5))
            (f
               [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
               (pi1 (ks (N 0)),
               (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                  (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
                  (rb (N 5)),
               sign
                 (bl
                    (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                    (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
                    (rb (N 5))) (pi2 (ks (N 0))) (rs (N 9))));
               (pi1 (ks (N 1)),
               (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                  (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
                  (rb (N 6)),
               sign
                 (bl
                    (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                    (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
                    (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))]), TWO)) }_2^^11,
      msg {(c 0 4, (ub (c 0 4) pk (bk 6) (x3tt 1 0), TWO)) }_ 2 ^^ 12]).
apply EQI_trans with (ml2:= [msg A, msg B, msg M, msg C1, msg C2, msg C3, msg ONE, msg TWO, msg THREE, msg (vk 0), msg (vk 1), 
       msg (pke 2), msg (tr 0 1 3 5 9), msg (tr 1 0 4 6 10), bol (to (x3tt 1 0)) #? A, bol (acpt 1 3 5 (x3tt 1 0)),
       bol (acpt 0 4 6 (x3tt 1 0)), msg {z (c 0 3, (ub (c 0 3) pk (bk 5) (x3tt 0 1), TWO)) }_ 2 ^^ 13,
       msg {z (c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO)) }_ 2 ^^ 14]).
assumption. apply H.
repeat (split; try reflexivity). 
clear - H0. unfold theta. 
funapptrmhypbl (msg x1) (msg x1) H0; simpl; try reflexivity.
funapptrmhypbl (msg (to x1)) (msg (to x1)) H0; simpl; try reflexivity.
funapptrmhypbl (bol ((to x1) #? A)) (bol ((to x1) #? A)) H0; simpl; try reflexivity.

funapptrmhypbl (msg (v 0)) (msg (v 0)) H0;simpl; try reflexivity.
funapptrmhypbl (bol (vcheck (v 0))) (bol (vcheck (v 0))) H0;simpl; try reflexivity.
funapptrmhypbl (msg (v 1)) (msg (v 1)) H0;simpl; try reflexivity.
funapptrmhypbl (bol (vcheck (v 1))) (bol (vcheck (v 1))) H0;simpl; try reflexivity.
funapptrmhypbl (bol (vcheck (v 0))& (vcheck (v 1))) (bol (vcheck (v 0))& (vcheck (v 1))) H0; simpl; try reflexivity.
simpl.

funapptrmhypbl (msg (x2t 0)) (msg (x2t 1)) H0; simpl; try reflexivity.
funapptrmhypbl (msg (to (x2t 0))) (msg (to (x2t 1))) H0; simpl; try reflexivity. 
funapptrmhypbl (bol ((to (x2t 0)) #? B)) (bol ((to (x2t 1)) #? B)) H0; simpl; try reflexivity. 
funapp_andB_in 22 27 H0. simpl.
funapp_andB_in 31 28 H0.

  
funapptrmhypbl (msg (x4ttt 0 1)) (msg (x4ttt 1 0)) H0; simpl; try reflexivity.
 funapptrmhypbl (msg (to (x4ttt 0 1))) (msg (to (x4ttt 1 0))) H0; simpl; try reflexivity.
funapptrmhypbl (bol (to (x4ttt 0 1)) #? B) (bol (to (x4ttt 1 0)) #?B) H0; simpl; try reflexivity.

restrsublis H0; simpl; try auto. 
simpl; repeat try auto. reflexivity.  reflexivity. reflexivity.
Qed.

