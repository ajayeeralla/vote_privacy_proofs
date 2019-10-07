 Require Export voting. 

Theorem frame4ind: (phi4 0 1) ~ (phi4 1 0).
Proof.  
unfold phi4, phi3, phi2, phi1.
unfold t1, t2, t3, t4.
simpl.
apply IFBRANCH_M4 with (ml1:= phi0) (ml2:= phi0).
simpl. unfold Avote. 
apply IFBRANCH_M3 with (ml1:= (phi0 ++ [bol (theta x1 A), msg (tr 0 0 3 5 9)]))(ml2:= (phi0 ++ [bol (theta x1 A), msg (tr 0 1 3 5 9)])). 
apply IFBRANCH_M2 with (ml1:= (phi0 ++ [bol (theta x1 A), msg (tr 0 0 3 5 9), bol (theta (x2t 0) B), msg (tr 1 1 4 6 10)]))(ml2:= (phi0 ++ [bol (theta x1 A), msg (tr 0 1 3 5 9), bol (theta (x2t 1) B), msg (tr 1 0 4 6 10)])).

 
apply IFBRANCH_M2 with (ml1:= (phi0 ++ [bol (theta x1 A), msg (tr 0 0 3 5 9), bol (theta (x2t 0) B), msg (tr 1 1 4 6 10), bol (to (x3tt 0 1)) #? A]))(ml2:= (phi0 ++ [bol (theta x1 A), msg (tr 0 1 3 5 9), bol (theta (x2t 1) B), msg (tr 1 0 4 6 10), bol (to (x3tt 1 0)) #? A])).
 
apply IFBRANCH_M1 with (ml1:= (phi0 ++ [bol (theta x1 A), msg (tr 0 0 3 5 9), bol (theta (x2t 0) B), msg (tr 1 1 4 6 10), bol (to (x3tt 0 1)) #? A, bol (acpt 0 3 5 (x3tt 0 1)), msg (e 0 3 5 (x3tt 0 1) TWO 11)]))(ml2:= (phi0 ++ [bol (theta x1 A), msg (tr 0 1 3 5 9), bol (theta (x2t 1) B), msg (tr 1 0 4 6 10), bol (to (x3tt 1 0)) #? A, bol (acpt 1 3 5 (x3tt 1 0)), msg (e 1 3 5 (x3tt 1 0) TWO 11)])).

apply IFBRANCH_M1 with (ml1:= (phi0 ++ [bol (theta x1 A), msg (tr 0 0 3 5 9), bol (theta (x2t 0) B), msg (tr 1 1 4 6 10), bol (to (x3tt 0 1)) #? A, bol (acpt 0 3 5 (x3tt 0 1)), msg (e 0 3 5 (x3tt 0 1) TWO 11), bol (to (x4ttt 0 1)) #? B]))(ml2:= (phi0 ++ [bol (theta x1 A), msg (tr 0 1 3 5 9), bol (theta (x2t 1) B), msg (tr 1 0 4 6 10), bol (to (x3tt 1 0)) #? A, bol (acpt 1 3 5 (x3tt 1 0)), msg (e 1 3 5 (x3tt 1 0) TWO 11), bol (to (x4ttt 1 0)) #? B])).
simpl. unfold theta, tr, e.
apply frame4goal1.
(** first goal end **)   
(** Goal: 2**)
simpl.
pose proof(frame4goal1).
funappmconst O H; auto.
restrsublis H; simpl; auto.
                         
(** Goal: 3**)

simpl.
pose proof(frame4goal1).
funappmconst O H; auto.
restrsublis H; simpl; auto.
(** Goal: 4**)
simpl.
pose proof(frame4goal1).
funappmconst O H; auto.
restrsublis H; simpl; auto.

(** Goal: 5**)
simpl.
pose proof(frame4goal1).
funappmconst O H; auto.
restrsublis H; simpl; auto.

(** Goal: 6 *)

simpl.
pose proof(frame4goal1).
funappmconst O H; auto.
restrsublis H; simpl; auto.

(** First [else] Branch *)
simpl.
apply IFBRANCH_M4 with (ml1:= phi0++[ bol (theta x1 A)]) (ml2:= phi0 ++ [  bol (theta x1 A)]).
unfold Bvote.
apply IFBRANCH_M3 with (ml1:= phi0++[ bol (theta x1 A), bol (theta x1 B), msg (tr 1 1 4 6 10) ]) (ml2:= phi0 ++ [  bol (theta x1 A), bol (theta x1 B), msg (tr 1 0 4 6 10)]).

apply IFBRANCH_M2 with (ml1:= phi0++[bol (theta x1 A), bol (theta x1 B), msg (tr 1 1 4 6 10), bol (theta (x2ft 1) A), msg (tr 0 0 3 5 9)]) (ml2:= phi0 ++ [bol (theta x1 A), bol (theta x1 B), msg (tr 1 0 4 6 10), bol (theta (x2ft 0) A), msg (tr 0 1 3 5 9)]).
simpl.

apply IFBRANCH_M2 with (ml1:= phi0++[bol (theta x1 A), bol (theta x1 B), msg (tr 1 1 4 6 10), bol (theta (x2ft 1) A), msg (tr 0 0 3 5 9), bol (to (x3ftt 0 1)) #? B]) (ml2:= phi0 ++ [bol (theta x1 A), bol (theta x1 B), msg (tr 1 0 4 6 10), bol (theta (x2ft 0) A), msg (tr 0 1 3 5 9), bol (to (x3ftt 1 0)) #? B]).

apply IFBRANCH_M1 with (ml1:= phi0++[bol (theta x1 A), bol (theta x1 B), msg (tr 1 1 4 6 10), bol (theta (x2ft 1) A), msg (tr 0 0 3 5 9), bol (to (x3ftt 0 1)) #? B, bol (acpt 1 4 6 (x3ftt 0 1)), msg (e 1 4 6 (x3ftt 0 1) TWO 11)]) (ml2:= phi0 ++ [bol (theta x1 A), bol (theta x1 B), msg (tr 1 0 4 6 10), bol (theta (x2ft 0) A), msg (tr 0 1 3 5 9), bol (to (x3ftt 1 0)) #? B, bol (acpt 0 4 6 (x3ftt 1 0)), msg (e 0 4 6 (x3ftt 1 0) TWO 11)]).

apply IFBRANCH_M1 with (ml1:= phi0++[bol (theta x1 A), bol (theta x1 B), msg (tr 1 1 4 6 10), bol (theta (x2ft 1) A), msg (tr 0 0 3 5 9), bol (to (x3ftt 0 1)) #? B, bol (acpt 1 4 6 (x3ftt 0 1)), msg (e 1 4 6 (x3ftt 0 1) TWO 11), bol (to (x4fttt 0 1)) #? A]) (ml2:= phi0 ++ [bol (theta x1 A), bol (theta x1 B), msg (tr 1 0 4 6 10), bol (theta (x2ft 0) A), msg (tr 0 1 3 5 9), bol (to (x3ftt 1 0)) #? B, bol (acpt 0 4 6 (x3ftt 1 0)), msg (e 0 4 6 (x3ftt 1 0) TWO 11), bol (to (x4fttt 1 0)) #? A]).
 (** similarly we can prove this branch *)
Admitted.




                Theorem frame5TraceInd:
                let u:= (c 0 3, (ub (c 0 3) pk (bk 5) (x3tt 0 1), TWO)) in
                let u':= (c 1 3, (ub (c 1 3) pk (bk 5) (x3tt 1 0), TWO)) in
                let v:= (c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO)) in
                let v':= (c 0 4, (ub (c 0 4) pk (bk 6) (x3tt 1 0), TWO)) in
   [msg A, msg B, msg M, msg C1, msg C2, msg C3, msg ONE, msg TWO, msg THREE, msg (vk 0), msg (vk 1), 
   msg (pke 2), bol (theta x1 A), msg (tr 0 0 3 5 9), bol (theta (x2t 0) B), msg (tr 1 1 4 6 10), 
   bol (to (x3tt 0 1)) #? A, bol (acpt 0 3 5 (x3tt 0 1)),
   msg {u}_ 2 ^^ 11, bol (to (x4ttt 0 1)) #? B,
   bol (acpt 1 4 6 (x3tt 0 1)), msg {v}_ 2 ^^ 12,
   bol (to (x5t 0 1)) #? M, bol (tau 1 (x5t 0 1)) #? {u}_ 2 ^^ 11,
   bol (tau 2 (x5t 0 1)) #? {v}_ 2 ^^ 12,
   bol (!((tau 3 (x5t 0 1)) #? {u}_ 2 ^^ 11)) & (!((tau 3 (x5t 0 1)) #? {v}_ 2 ^^ 12)),
   bol ((tau 3 u)#? TWO) & ((tau 3 v) #? TWO) & ((tau 3 (dec (tau 3 (x5t 0 1)) (ske 2))) #? TWO), msg (shufl ((tau 1 u), (tau 2 u)) ((tau 1 v), (tau 2 v)) ((tau 1 (dec (tau 3 (x5t 0 1)) (ske 2))),  (tau 2 (dec (tau 3 (x5t 0 1)) (ske 2)))))] ~

[msg A, msg B, msg M, msg C1, msg C2, msg C3, msg ONE, msg TWO, msg THREE, msg (vk 0), msg (vk 1), 
   msg (pke 2), bol (theta x1 A), msg (tr 0 1 3 5 9), bol (theta (x2t 1) B), msg (tr 1 0 4 6 10), 
   bol (to (x3tt 1 0)) #? A, bol (acpt 1 3 5 (x3tt 1 0)),
   msg {u'}_2 ^^ 11, bol (to (x4ttt 1 0)) #? B,
   bol (acpt 0 4 6 (x3tt 1 0)), msg {v'}_ 2 ^^ 12,
   bol (to (x5t 1 0)) #? M, bol (tau 1 (x5t 1 0)) #? {u'}_ 2 ^^ 11,
   bol (tau 2 (x5t 1 0)) #? {v'}_ 2 ^^ 12,
   bol (!((tau 3 (x5t 1 0)) #? {u'}_ 2 ^^ 11)) & (! ((tau 3 (x5t 1 0)) #? {v'}_ 2 ^^ 12)),
   bol ((tau 3 u')#? TWO) & ((tau 3 v') #? TWO) & ((tau 3 (dec (tau 3 (x5t 1 0)) (ske 2))) #? TWO), msg (shufl ((tau 1 u'), (tau 2 u')) ((tau 1 v'), (tau 2 v')) ((tau 1 (dec (tau 3 (x5t 1 0)) (ske 2))),  (tau 2 (dec (tau 3 (x5t 1 0)) (ske 2)))))].
Proof. simpl. repeat rewrite proj1, proj2.
Axiom eqmref: forall m, m#?m ## TRue.
repeat rewrite eqmref.
repeat rewrite andB_TRue_l.
Eval compute in x4ttt 0 1.
Eval compute in (tr 0 0 3  5 9).
Definition tr03x := ((vk 0), ((Mvar 5), (sign (Mvar 5) (ssk 0) (rs (N 9))))).
Definition tr14x :=  ((vk 1), ((Mvar 6), (sign (Mvar 6) (ssk 1) (rs (N 10))))).
Definition x4tttex := (f (toListm (phi0 ++ [msg (tr 0 0 3  5 9), msg (tr 1 1 4 6 10), msg (Mvar 0) ]))).

Definition x5tex := f (toListm (phi0 ++ [msg (tr 0 0 3  5 9), msg (tr 1 1 4 6 10), msg (Mvar 0), msg (Mvar 1) ])).

pose proof(EXTENCCCA2 (tau 1 (x5t 0 1)) (c 0 3, (ub (c 0 3) pk (bk 5) (x3tt 0 1), TWO)) (z (c 0 3, (ub (c 0 3) pk (bk 5) (x3tt 0 1), TWO))) O (c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO)) (z (c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO))) O 0 1 2 11 12 13 14 
[ msg (dec (pi2 (pi2 x5tex)) (ske 2)), msg (c 0 3, ub (c 0 3) pk (bk 5) (x3tt 0 1)), msg (c 1 4, ub (c 1 4) pk (bk 6) (x3tt 0 1)), msg A, msg B, msg M, msg C1, msg C2, msg C3, msg ONE, 
 msg TWO, msg THREE, msg (vk 0), msg (vk 1), msg (pke 2),
 msg (Mvar 0), msg (Mvar 1), msg (ssk 0), msg (ssk 1), msg (sr 9), msg (sr 10), 
 msg (tr 0 0 3 5 9), 
   msg (tr 1 1 4 6 10), msg (x3tt 0 1), msg x4tttex, msg x5tex,  bol (acpt 0 3 5 (x3tt 0 1)),
   bol (acpt 1 4 6 (x3tt 0 1)) ]).
simpl in H. 
do 2  rewrite zeroEql1 in H; try rewrite refEql.
simpl.  do 4 rewrite IFTRUE_M in H. simpl.


(** Substitution: x <- s in l, x is of type variable, l is of type [mylist] *)

Definition submsg_mylist (n:nat)(s:message) {m} (l:mylist m):mylist m :=
  match l with
  | [] => []
  | a : h =>  (submsg_os n s a) : (submsg_mylist n s h)
  end.

Axiom gen_prop4:  forall {n m} (n1 n2 n3 n4:nat) (t t0 t1: message) (z: mylist n) (z1:mylist m), let v0 := (V0 (f (toListm z))) in
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
                 let rt1 := (((ub c10 t r0 t5), (c10, k0)), ((ub c01 t r1 t4), (c01, k1))) in
                 let rt2 := ((ub c10 t r0 t4), (c10, |_)) in 
                 let rt3 := (|_, ((ub c01 t r1 t5), c01)) in
                 let lz1 := (submsg_mylist 5 (bl c00 t r0) (submsg_mylist 6 (bl c11 t r1) z1)) in
                 let rz1 := (submsg_mylist 5 (bl c10 t r0) (submsg_mylist 6 (bl c01 t r1) z1)) in
                
                 
                 (z++ lz1++[msg (bl c00 t r0), msg (bl c11 t r1), bol (acc c00 t r0 t2)& (acc c11 t r1 t3), bol (acc c00 t r0 t2), bol (acc c11 t r1 t3), msg lt1])
                      
                    ~
                   
                    (z++rz1++[msg (bl c10 t r0), msg (bl c01 t r1), bol (acc c10 t r0 t4)& (acc c01 t r1 t5), bol (acc c10 t r0 t4), bol (acc c01 t r1 t5), msg rt1]).
Definition x4tttbx := (f (toListm (phi0 ++ [msg tr03x, msg tr14x, msg {(z (c 0 3, (ub (c 0 3) pk (bk 5) x3ttx, TWO)))}_ 2 ^^ 13 ]))).

Definition x5tbx := f (toListm (phi0 ++ [msg tr03x, msg tr14x, msg {(z (c 0 3, (ub (c 0 3) pk (bk 5) x3ttx, TWO)))}_ 2 ^^ 13,  msg {z (c 1 4, (ub (c 1 4) pk (bk 6) x3ttx, TWO)) }_ 2 ^^ 14])).

pose proof (gen_prop4 5 6 3 4 (pubkey x1) (x3ttx) (x3ttx) phi0 [msg {(z (c 0 3, (ub (c 0 3) pk (bk 5) (x3tt 0 1), TWO)))}_ 2 ^^ 13,  msg {z (c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO)) }_ 2 ^^ 14, msg (ssk 0), msg (ssk 1), msg (sr 9), msg (sr 10), msg (ske 2), msg tr03x, msg tr14x, msg x3ttx, msg x4tttbx, msg x5tbx]). unfold distMvars in H0. 
 simpl in H0. 
 unfold Fresh in H0; simpl in H0.
 rewrite voteEql in H0.
restr_proj_in 27 H0; simpl; try split; auto.
funappf1 pi1 29 H0.
funappf1 pi2 30 H0.
rewrite proj1, proj2 in H0.
dropLast_in H0.
funappf1 (tau 1) 1 H0.
funappf1 (tau 2) 2 H0.
funappf1 (tau 3) 3 H0.
repeat rewrite proj1, proj2 in H0.
dropone_in H0.

funappf2m pair 1 2 H0.
do 3 restrproj_in 2 H0.

funappf1 (tau 1) 2 H0.
funappf1 (tau 2) 3 H0.
funappf1 (tau 3) 4 H0.
repeat rewrite proj1, proj2 in H0.
dropone_in H0.

funappf2m pair 1 2 H0.
do 2 restrproj_in 2 H0.

restrproj_in 3 H0.

(** constructing dec term *) 
funappf1 pi2 26 H0. 
funappf1 pi2 1 H0; restrproj_in 2 H0.
funappf2m dec 1 22 H0.
restrproj_in 2 H0.
(** delete the secret key from clear*)
restrproj_in 22 H0. 
restrproj_in 28 H0.
restrproj_in 27 H0.


(** l1 ++[e1]++[e2] ~ l1 ++ [z(e1)]++[z(e2)] /\  l1 ++ [z(e1)]++[z(e2)]~l2++[z(e1)]++[z(e2)] *)
simpl.
 


Eval compute in (submsg_msg 1 {(c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO)) }_ 2 ^^ 12 (submsg_msg 0 {( (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) , ((ub (c 0 3) pk (bk 5) (x3tt 0 1)), TWO)) }_ 2 ^^ 11 x5tex)).
 
assert( (x5t 0 1) # (submsg_msg 1 {(c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO)) }_ 2 ^^ 12 (submsg_msg 0 {( (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) , ((ub (c 0 3) pk (bk 5) (x3tt 0 1)), TWO)) }_ 2 ^^ 11 x5tex))).
simpl. reflexivity. 
rewrite <- H1 in H.

assert( (x4ttt 0 1) # (submsg_msg 1 {(c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO)) }_ 2 ^^ 12 (submsg_msg 0 {( (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) , ((ub (c 0 3) pk (bk 5) (x3tt 0 1)), TWO)) }_ 2 ^^ 11 x4tttex))).
simpl. reflexivity. 
rewrite <- H2 in H.
clear H1 H2.

simpl.

assert ( (submsg_msg 0 {( (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) , ((ub (c 0 3) pk (bk 5) (x3tt 0 1)), TWO)) }_ 2 ^^ 11 (Mvar 0)) # (submsg_msg 0 {( (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) , ((ub (c 0 3) pk (bk 5) (x3tt 0 1)), TWO)) }_ 2 ^^ 11 (Mvar 0))).
reflexivity.
rewrite H1 in H.
clear H1.





                            (** apply ENCCCA2 axiom 2nd time *)
Definition x4tttex' := (f (toListm (phi0 ++ [msg (tr 0 1 3  5 9), msg (tr 1 0 4 6 10), msg (Mvar 0) ]))).

Definition x5tex' := f (toListm (phi0 ++ [msg (tr 0 1 3  5 9), msg (tr 1 0 4 6 10), msg (Mvar 0), msg (Mvar 1) ])).
simpl.
pose proof(EXTENCCCA2 (tau 1 (x5t 0 1)) (z (c 0 3, (ub (c 0 3) pk (bk 5) (x3tt 0 1), TWO))) (c 1 3, (ub (c 1 3) pk (bk 5) (x3tt 1 0), TWO)) O (z (c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO))) (c 0 4, (ub (c 0 4) pk (bk 6) (x3tt 1 0), TWO))  O 0 1 2 13 14 11 12 
[msg (dec (pi2 (pi2 x5tex')) (ske 2)), msg ((c 1 3), (ub (c 1 3) pk (r 5) (x3tt 1 0))),
 msg ((c 0 4), (ub (c 0 4) pk (r 6) (x3tt 1 0))), msg A, msg B, msg M, msg C1, msg C2, msg C3, 
 msg ONE, msg TWO, msg THREE, msg (vk 0), msg (vk 1), msg (pke 2), msg (Mvar 0), msg (Mvar 1), msg (ssk 0), msg (ssk 1), msg (sr 9), msg (sr 10),  msg (tr 0 1 3 5 9), 
   msg (tr 1 0 4 6 10), msg (x3tt 1 0), msg x4tttex', msg x5tex', bol (acc (c 1 3) pk (r 5) (x3tt 1 0)), bol (acc (c 0 4) pk (r 6) (x3tt 1 0))]).

simpl in H. 
 
assert( (| z (c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO)) |) #? (| (c 0 4, (ub (c 0 4) pk (bk 6) (x3tt 1 0), TWO)) |) ## TRue).
rewrite symEql.
apply zeroEql1. apply len_reg. 

   
pose proof (commEql 4 4 (V1 x1) (V0 x1)). 
rewrite symEql in H2. rewrite voteEql in H2. rewrite IFTRUE_B in H2.
rewrite symEql.
apply H2.

repeat (try split; try unfold Fresh; try auto). auto. auto. 
apply len_reg.


apply ubEql.

pose proof (commEql 4 4 (V1 x1) (V0 x1)).
rewrite symEql in H2. rewrite voteEql in H2. rewrite IFTRUE_B in H2.
rewrite symEql.
apply H2.

try split; try unfold Fresh; simpl; try auto. reflexivity.
simpl.
reflexivity; try apply refEql; auto.
 apply refEql.
apply refEql.
apply len_prev_comp.
apply refEql.
rewrite H2 in H1.

assert ( (|z (c 0 3, (ub (c 0 3) pk (bk 5) (x3tt 0 1), TWO))|#? |(c 1 3, (ub (c 1 3) pk (bk 5) (x3tt 1 0), TWO))|) ## TRue).

rewrite symEql. 
apply zeroEql1. apply len_reg. 
    
pose proof (commEql 3 3 (V1 x1) (V0 x1)).
rewrite symEql, voteEql, IFTRUE_B in H3. apply H3.

try split; try unfold Fresh; simpl; try reflexivity. auto.
reflexivity.
apply len_reg.
apply ubEql.

pose proof (commEql 3 3 (V1 x1) (V0 x1)).
rewrite symEql, voteEql, IFTRUE_B in H3. 
apply H3.

try split; try reflexivity. unfold Fresh. simpl. reflexivity.
simpl.
reflexivity.
apply refEql. apply refEql.
apply len_prev_comp.
apply refEql. repeat rewrite IFTRUE_M in H1. simpl in H1.
repeat rewrite H3 in H1.
clear H3 H2.

repeat rewrite IFTRUE_M in H1.  
 

 

(** l1 ++ [e1]++[e2] ~ l1 ++ [z(e1)]++[z(e2)]~l2 ++ [z(e1)]++[z(e2)]~ l2 ++ [e1']++[e2'] *)




assert(ftran: [msg (dec (pi2 (pi2 (x5t 0 1))) (pi2 (ke (N 2)))),
       msg
         (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)),
         ub (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
           (rb (N 5))
           (f
              [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
              (pi1 (ks (N 0)),
              (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                 (rb (N 5)),
              sign
                (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                   (rb (N 5))) (pi2 (ks (N 0))) (rs (N 9))));
              (pi1 (ks (N 1)),
              (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                 (rb (N 6)),
              sign
                (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                   (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))])),
       msg
         (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)),
         ub (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
           (rb (N 6))
           (f
              [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
              (pi1 (ks (N 0)),
              (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                 (rb (N 5)),
              sign
                (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                   (rb (N 5))) (pi2 (ks (N 0))) (rs (N 9))));
              (pi1 (ks (N 1)),
              (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                 (rb (N 6)),
              sign
                (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                   (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))])), msg A, msg B, msg M, msg C1, msg C2, msg C3, msg ONE, msg TWO, msg THREE, msg (pi1 (ks (N 0))), msg (pi1 (ks (N 1))), msg (pi1 (ke (N 2))),
       msg {(comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)), (ub (c 0 3) pk (bk 5) (x3tt 0 1), TWO)) }_ 2 ^^ 11,
       msg {(c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO)) }_ 2 ^^ 12, msg (pi2 (ks (N 0))), msg (pi2 (ks (N 1))), msg (rs (N 9)), msg (rs (N 10)),
       msg
         (pi1 (ks (N 0)),
         (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
            (rb (N 5)),
         sign
           (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
              (rb (N 5))) (pi2 (ks (N 0))) (rs (N 9)))),
       msg
         (pi1 (ks (N 1)),
         (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
            (rb (N 6)),
         sign
           (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
              (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10)))),
       msg
         (f
            [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
            (pi1 (ks (N 0)),
            (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
               (rb (N 5)),
            sign
              (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                 (rb (N 5))) (pi2 (ks (N 0))) (rs (N 9))));
            (pi1 (ks (N 1)),
            (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
               (rb (N 6)),
            sign
              (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                 (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))]), msg (x4ttt 0 1), msg (x5t 0 1),
       bol
         (acc (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
            (rb (N 5))
            (f
               [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
               (pi1 (ks (N 0)),
               (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                  (rb (N 5)),
               sign
                 (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                    (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 5))) (pi2 (ks (N 0))) (rs (N 9))));
               (pi1 (ks (N 1)),
               (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                  (rb (N 6)),
               sign
                 (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                    (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))])),
       bol
         (acc (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
            (rb (N 6))
            (f
               [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
               (pi1 (ks (N 0)),
               (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                  (rb (N 5)),
               sign
                 (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                    (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 5))) (pi2 (ks (N 0))) (rs (N 9))));
               (pi1 (ks (N 1)),
               (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                  (rb (N 6)),
               sign
                 (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                    (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))]))] ~ [msg
          (dec
             (pi2
                (pi2
                   (f
                      [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
                      (pi1 (ks (N 0)),
                      (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5),
                      sign (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5)) (pi2 (ks (N 0))) (rs (N 9))));
                      (pi1 (ks (N 1)),
                      (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                         (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6)),
                      sign
                        (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                           (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))));
                      {z
                         (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)),
                         (ub (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                            (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 5))
                            (f
                               [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
                               (pi1 (ks (N 0)),
                               (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5),
                               sign (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5)) (pi2 (ks (N 0))) (rs (N 9))));
                               (pi1 (ks (N 1)),
                               (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                                  (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6)),
                               sign
                                 (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                                    (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))]), TWO)) }_ 2 ^^ 
                      13;
                      {z
                         (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)),
                         (ub (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                            (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6))
                            (f
                               [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
                               (pi1 (ks (N 0)),
                               (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5),
                               sign (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5)) (pi2 (ks (N 0))) (rs (N 9))));
                               (pi1 (ks (N 1)),
                               (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                                  (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6)),
                               sign
                                 (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                                    (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))]), TWO)) }_ 2 ^^ 
                      14]))) (pi2 (ke (N 2)))),
       msg
         (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3)),
         ub (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5)
           (f
              [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
              (pi1 (ks (N 0)),
              (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5),
              sign (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5)) (pi2 (ks (N 0))) (rs (N 9))));
              (pi1 (ks (N 1)),
              (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                 (rb (N 6)),
              sign
                (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                   (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))])),
       msg
         (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 4)),
         ub (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 4))) (pubkey x1) (r 6)
           (f
              [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
              (pi1 (ks (N 0)),
              (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5),
              sign (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5)) (pi2 (ks (N 0))) (rs (N 9))));
              (pi1 (ks (N 1)),
              (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                 (rb (N 6)),
              sign
                (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                   (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))])), msg A, msg B, msg M, msg C1, msg C2, msg C3, msg ONE, msg TWO, msg THREE, msg (vk 0), msg (vk 1), msg (pke 2),
       msg
         {z
            (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)),
            (ub (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
               (rb (N 5))
               (f
                  [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
                  (pi1 (ks (N 0)),
                  (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                     (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 5)),
                  sign
                    (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                       (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 5))) (pi2 (ks (N 0))) (rs (N 9))));
                  (pi1 (ks (N 1)),
                  (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                     (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6)),
                  sign
                    (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                       (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))]), TWO)) }_ 2 ^^ 13,
       msg
         {z
            (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)),
            (ub (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
               (rb (N 6))
               (f
                  [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
                  (pi1 (ks (N 0)),
                  (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                     (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 5)),
                  sign
                    (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                       (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 5))) (pi2 (ks (N 0))) (rs (N 9))));
                  (pi1 (ks (N 1)),
                  (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                     (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6)),
                  sign
                    (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                       (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))]), TWO)) }_ 2 ^^ 14, 
       msg (pi2 (ks (N 0))), msg (pi2 (ks (N 1))), msg (rs (N 9)), msg (rs (N 10)),
       msg
         (pi1 (ks (N 0)),
         (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5),
         sign (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5)) (pi2 (ks (N 0))) (rs (N 9)))),
       msg
         (pi1 (ks (N 1)),
         (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
            (rb (N 6)),
         sign
           (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
              (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10)))),
       msg
         (f
            [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
            (pi1 (ks (N 0)),
            (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5),
            sign (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5)) (pi2 (ks (N 0))) (rs (N 9))));
            (pi1 (ks (N 1)),
            (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
               (rb (N 6)),
            sign
              (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                 (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))]),
       msg
         (f
            [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
            (pi1 (ks (N 0)),
            (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5),
            sign (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5)) (pi2 (ks (N 0))) (rs (N 9))));
            (pi1 (ks (N 1)),
            (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
               (rb (N 6)),
            sign
              (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                 (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))));
            {z
               (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)),
               (ub (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                  (rb (N 5))
                  (f
                     [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
                     (pi1 (ks (N 0)),
                     (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5),
                     sign (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5)) (pi2 (ks (N 0))) (rs (N 9))));
                     (pi1 (ks (N 1)),
                     (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                        (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6)),
                     sign
                       (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                          (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))]), TWO)) }_ 2 ^^ 13]),
       msg
         (f
            [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
            (pi1 (ks (N 0)),
            (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5),
            sign (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5)) (pi2 (ks (N 0))) (rs (N 9))));
            (pi1 (ks (N 1)),
            (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
               (rb (N 6)),
            sign
              (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                 (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))));
            {z
               (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)),
               (ub (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                  (rb (N 5))
                  (f
                     [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
                     (pi1 (ks (N 0)),
                     (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5),
                     sign (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5)) (pi2 (ks (N 0))) (rs (N 9))));
                     (pi1 (ks (N 1)),
                     (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                        (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6)),
                     sign
                       (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                          (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))]), TWO)) }_ 2 ^^ 13;
            {z
               (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)),
               (ub (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                  (rb (N 6))
                  (f
                     [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
                     (pi1 (ks (N 0)),
                     (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5),
                     sign (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5)) (pi2 (ks (N 0))) (rs (N 9))));
                     (pi1 (ks (N 1)),
                     (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                        (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6)),
                     sign
                       (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                          (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))]), TWO)) }_ 2 ^^ 14]),
       bol
         (acc (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5)
            (f
               [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
               (pi1 (ks (N 0)),
               (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5),
               sign (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5)) (pi2 (ks (N 0))) (rs (N 9))));
               (pi1 (ks (N 1)),
               (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                  (rb (N 6)),
               sign
                 (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                    (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))])),
       bol
         (acc (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 4))) (pubkey x1) (r 6)
            (f
               [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
               (pi1 (ks (N 0)),
               (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5),
               sign (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5)) (pi2 (ks (N 0))) (rs (N 9))));
               (pi1 (ks (N 1)),
               (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                  (rb (N 6)),
               sign
                 (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                    (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))]))]).
apply EQI_trans with (ml2:= [msg
         (dec
            (pi2
               (pi2
                  (f
                     [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
                     (pi1 (ks (N 0)),
                     (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                        (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 5)),
                     sign
                       (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                          (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 5))) (pi2 (ks (N 0))) (rs (N 9))));
                     (pi1 (ks (N 1)),
                     (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                        (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6)),
                     sign
                       (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                          (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))));
                     {z
                        (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)),
                        (ub (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                           (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 5))
                           (f
                              [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
                              (pi1 (ks (N 0)),
                              (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                                 (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 5)),
                              sign
                                (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                                   (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 5))) (pi2 (ks (N 0))) (rs (N 9))));
                              (pi1 (ks (N 1)),
                              (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                                 (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6)),
                              sign
                                (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                                   (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))]), TWO)) }_ 2 ^^ 
                     13; {z (c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO)) }_ 2 ^^ 14]))) (pi2 (ke (N 2)))),
      msg
        (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)),
        ub (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
          (rb (N 5))
          (f
             [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
             (pi1 (ks (N 0)),
             (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                (rb (N 5)),
             sign
               (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                  (rb (N 5))) (pi2 (ks (N 0))) (rs (N 9))));
             (pi1 (ks (N 1)),
             (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                (rb (N 6)),
             sign
               (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                  (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))])),
      msg
        (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)),
        ub (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
          (rb (N 6))
          (f
             [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
             (pi1 (ks (N 0)),
             (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                (rb (N 5)),
             sign
               (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                  (rb (N 5))) (pi2 (ks (N 0))) (rs (N 9))));
             (pi1 (ks (N 1)),
             (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                (rb (N 6)),
             sign
               (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                  (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))])), msg A, msg B, msg M, msg C1, msg C2, msg C3, msg ONE, msg TWO, msg THREE, msg (pi1 (ks (N 0))), msg (pi1 (ks (N 1))), msg (pi1 (ke (N 2))),
      msg
        {z
           (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)),
           (ub (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
              (rb (N 5))
              (f
                 [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
                 (pi1 (ks (N 0)),
                 (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                    (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 5)),
                 sign
                   (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                      (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 5))) (pi2 (ks (N 0))) (rs (N 9))));
                 (pi1 (ks (N 1)),
                 (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                    (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6)),
                 sign
                   (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                      (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))]), TWO)) }_ 2 ^^ 13,
      msg {z (c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO)) }_ 2 ^^ 14, msg (pi2 (ks (N 0))), msg (pi2 (ks (N 1))), msg (rs (N 9)), msg (rs (N 10)),
      msg
        (pi1 (ks (N 0)),
        (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
           (rb (N 5)),
        sign
          (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
             (rb (N 5))) (pi2 (ks (N 0))) (rs (N 9)))),
      msg
        (pi1 (ks (N 1)),
        (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
           (rb (N 6)),
        sign
          (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
             (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10)))),
      msg
        (f
           [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
           (pi1 (ks (N 0)),
           (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
              (rb (N 5)),
           sign
             (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                (rb (N 5))) (pi2 (ks (N 0))) (rs (N 9))));
           (pi1 (ks (N 1)),
           (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
              (rb (N 6)),
           sign
             (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))]),
      msg
        (f
           [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
           (pi1 (ks (N 0)),
           (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
              (rb (N 5)),
           sign
             (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                (rb (N 5))) (pi2 (ks (N 0))) (rs (N 9))));
           (pi1 (ks (N 1)),
           (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
              (rb (N 6)),
           sign
             (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))));
           {z
              (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)),
              (ub (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                 (rb (N 5))
                 (f
                    [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
                    (pi1 (ks (N 0)),
                    (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                       (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 5)),
                    sign
                      (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                         (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 5))) (pi2 (ks (N 0))) (rs (N 9))));
                    (pi1 (ks (N 1)),
                    (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                       (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6)),
                    sign
                      (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                         (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))]), TWO)) }_ 2 ^^ 13]),
      msg
        (f
           [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
           (pi1 (ks (N 0)),
           (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
              (rb (N 5)),
           sign
             (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                (rb (N 5))) (pi2 (ks (N 0))) (rs (N 9))));
           (pi1 (ks (N 1)),
           (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
              (rb (N 6)),
           sign
             (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))));
           {z
              (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)),
              (ub (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                 (rb (N 5))
                 (f
                    [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
                    (pi1 (ks (N 0)),
                    (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                       (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 5)),
                    sign
                      (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                         (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 5))) (pi2 (ks (N 0))) (rs (N 9))));
                    (pi1 (ks (N 1)),
                    (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                       (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6)),
                    sign
                      (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                         (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))]), TWO)) }_ 2 ^^ 13;
           {z (c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO)) }_ 2 ^^ 14]),
      bol
        (acc (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
           (rb (N 5))
           (f
              [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
              (pi1 (ks (N 0)),
              (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                 (rb (N 5)),
              sign
                (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                   (rb (N 5))) (pi2 (ks (N 0))) (rs (N 9))));
              (pi1 (ks (N 1)),
              (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                 (rb (N 6)),
              sign
                (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                   (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))])),
      bol
        (acc (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
           (rb (N 6))
           (f
              [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
              (pi1 (ks (N 0)),
              (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                 (rb (N 5)),
              sign
                (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                   (rb (N 5))) (pi2 (ks (N 0))) (rs (N 9))));
              (pi1 (ks (N 1)),
              (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                 (rb (N 6)),
              sign
                (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4))) (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                   (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))]))]).
apply H; try split; auto.


apply H0.

clear H. clear H0.



(** apply transition again *)

assert ( (x5t 1 0) # (submsg_msg 0 {(c 1 3, (ub (c 1 3) pk (bk 5) (x3tt 1 0), TWO)) }_ 2 ^^ 11 (submsg_msg 1 {(c 0 4, (ub (c 0 4) pk (bk 6) (x3tt 1 0), TWO)) }_ 2 ^^ 12 (x5tex')))).
reflexivity.
rewrite <- H in H1.

simpl.  

assert (   {z
                          (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)),
                          (ub (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                             (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 5))
                             (f
                                [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
                                (pi1 (ks (N 0)),
                                (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                                   (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 5)),
                                sign
                                  (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                                     (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 5))) 
                                  (pi2 (ks (N 0))) (rs (N 9))));
                                (pi1 (ks (N 1)),
                                (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                                   (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6)),
                                sign
                                  (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                                     (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6))) 
                                  (pi2 (ks (N 1))) (rs (N 10))))]), TWO)) }_ 2 ^^ 13 # {z
                            (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)),
                            (ub (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
                               (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 5))
                               (f
                                  [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
                                  (pi1 (ks (N 0)),
                                  (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5),
                                  sign (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5)) (pi2 (ks (N 0))) (rs (N 9))));
                                  (pi1 (ks (N 1)),
                                  (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                                     (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6)),
                                  sign
                                    (bl (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 4)))
                                       (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (rb (N 6))) 
                                    (pi2 (ks (N 1))) (rs (N 10))))]), TWO)) }_ 2 ^^ 13).
Axiom zeroEqlxy: forall x y,  (z x) # (z y).
rewrite zeroEqlxy with (x:= (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)),
     (ub
        (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)))
        (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
        (rb (N 5))
        (f
           [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
           (pi1 (ks (N 0)),
           (bl
              (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                 (kc (N 3)))
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
              (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                 (kc (N 4)))
              (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
              (rb (N 6)),
           sign
             (bl
                (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                   (kc (N 4)))
                (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))]), TWO))) (y:= (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) (kc (N 3)),
       (ub
          (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
             (kc (N 3)))
          (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))])) 
          (rb (N 5))
          (f
             [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
             (pi1 (ks (N 0)),
             (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) (pubkey x1) (r 5),
             sign
               (bl (comm (V1 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; vk 0; vk 1; pke 2])) (kc (N 3))) 
                  (pubkey x1) (r 5)) (pi2 (ks (N 0))) (rs (N 9))));
             (pi1 (ks (N 1)),
             (bl
                (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                   (kc (N 4)))
                (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                (rb (N 6)),
             sign
               (bl
                  (comm (V0 (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                     (kc (N 4)))
                  (pubkey (f [A; B; M; C1; C2; C3; ONE; TWO; THREE; pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
                  (rb (N 6))) (pi2 (ks (N 1))) (rs (N 10))))]), TWO))).

reflexivity.

rewrite H0 in H1.
rewrite H0 in ftran. clear H H0.
assert ({z (c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO)) }_ 2 ^^ 14 # {z (c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 1 0), TWO)) }_ 2 ^^ 14 ).
rewrite zeroEqlxy. reflexivity. rewrite H in ftran.
rewrite H in H1.
clear H. 

assert ( (x4ttt 1 0) # (submsg_msg 0  {(c 1 3, (ub (c 1 3) pk (bk 5) (x3tt 1 0), TWO)) }_ 2 ^^ 11 (submsg_msg 1 {(c 0 4, (ub (c 0 4) pk (bk 6) (x3tt 1 0), TWO)) }_ 2 ^^ 12 x4tttex'))).
reflexivity.
rewrite <- H in H1.

clear H.

assert ( [msg (dec (pi2 (pi2 (x5t 0 1))) (pi2 (ke (N 2)))),
           msg
             (comm
                (V0
                   (f
                      [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                      pi1 (ks (N 0)); pi1 (ks (N 1)); 
                      pi1 (ke (N 2))])) (kc (N 3)),
             ub
               (comm
                  (V0
                     (f
                        [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                        pi1 (ks (N 0)); pi1 (ks (N 1)); 
                        pi1 (ke (N 2))])) (kc (N 3)))
               (pubkey
                  (f
                     [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                     pi1 (ks (N 0)); pi1 (ks (N 1)); 
                     pi1 (ke (N 2))])) (rb (N 5))
               (f
                  [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                  pi1 (ks (N 0)); pi1 (ks (N 1)); 
                  pi1 (ke (N 2));
                  (pi1 (ks (N 0)),
                  (bl
                     (comm
                        (V0
                           (f
                              [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                              pi1 (ks (N 0)); pi1 (ks (N 1));
                              pi1 (ke (N 2))])) (kc (N 3)))
                     (pubkey
                        (f
                           [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                           pi1 (ks (N 0)); pi1 (ks (N 1)); 
                           pi1 (ke (N 2))])) (rb (N 5)),
                  sign
                    (bl
                       (comm
                          (V0
                             (f
                                [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                pi1 (ks (N 0)); pi1 (ks (N 1));
                                pi1 (ke (N 2))])) 
                          (kc (N 3)))
                       (pubkey
                          (f
                             [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                             pi1 (ks (N 0)); pi1 (ks (N 1)); 
                             pi1 (ke (N 2))])) (rb (N 5))) 
                    (pi2 (ks (N 0))) (rs (N 9))));
                  (pi1 (ks (N 1)),
                  (bl
                     (comm
                        (V1
                           (f
                              [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                              pi1 (ks (N 0)); pi1 (ks (N 1));
                              pi1 (ke (N 2))])) (kc (N 4)))
                     (pubkey
                        (f
                           [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                           pi1 (ks (N 0)); pi1 (ks (N 1)); 
                           pi1 (ke (N 2))])) (rb (N 6)),
                  sign
                    (bl
                       (comm
                          (V1
                             (f
                                [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                pi1 (ks (N 0)); pi1 (ks (N 1));
                                pi1 (ke (N 2))])) 
                          (kc (N 4)))
                       (pubkey
                          (f
                             [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                             pi1 (ks (N 0)); pi1 (ks (N 1)); 
                             pi1 (ke (N 2))])) (rb (N 6))) 
                    (pi2 (ks (N 1))) (rs (N 10))))])),
           msg
             (comm
                (V1
                   (f
                      [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                      pi1 (ks (N 0)); pi1 (ks (N 1)); 
                      pi1 (ke (N 2))])) (kc (N 4)),
             ub
               (comm
                  (V1
                     (f
                        [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                        pi1 (ks (N 0)); pi1 (ks (N 1)); 
                        pi1 (ke (N 2))])) (kc (N 4)))
               (pubkey
                  (f
                     [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                     pi1 (ks (N 0)); pi1 (ks (N 1)); 
                     pi1 (ke (N 2))])) (rb (N 6))
               (f
                  [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                  pi1 (ks (N 0)); pi1 (ks (N 1)); 
                  pi1 (ke (N 2));
                  (pi1 (ks (N 0)),
                  (bl
                     (comm
                        (V0
                           (f
                              [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                              pi1 (ks (N 0)); pi1 (ks (N 1));
                              pi1 (ke (N 2))])) (kc (N 3)))
                     (pubkey
                        (f
                           [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                           pi1 (ks (N 0)); pi1 (ks (N 1)); 
                           pi1 (ke (N 2))])) (rb (N 5)),
                  sign
                    (bl
                       (comm
                          (V0
                             (f
                                [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                pi1 (ks (N 0)); pi1 (ks (N 1));
                                pi1 (ke (N 2))])) 
                          (kc (N 3)))
                       (pubkey
                          (f
                             [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                             pi1 (ks (N 0)); pi1 (ks (N 1)); 
                             pi1 (ke (N 2))])) (rb (N 5))) 
                    (pi2 (ks (N 0))) (rs (N 9))));
                  (pi1 (ks (N 1)),
                  (bl
                     (comm
                        (V1
                           (f
                              [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                              pi1 (ks (N 0)); pi1 (ks (N 1));
                              pi1 (ke (N 2))])) (kc (N 4)))
                     (pubkey
                        (f
                           [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                           pi1 (ks (N 0)); pi1 (ks (N 1)); 
                           pi1 (ke (N 2))])) (rb (N 6)),
                  sign
                    (bl
                       (comm
                          (V1
                             (f
                                [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                pi1 (ks (N 0)); pi1 (ks (N 1));
                                pi1 (ke (N 2))])) 
                          (kc (N 4)))
                       (pubkey
                          (f
                             [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                             pi1 (ks (N 0)); pi1 (ks (N 1)); 
                             pi1 (ke (N 2))])) (rb (N 6))) 
                    (pi2 (ks (N 1))) (rs (N 10))))])), 
           msg A, msg B, msg M, msg C1, msg C2, msg C3, 
           msg ONE, msg TWO, msg THREE, msg (pi1 (ks (N 0))),
           msg (pi1 (ks (N 1))), msg (pi1 (ke (N 2))),
           msg
             {(comm
                 (V0
                    (f
                       [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                       pi1 (ks (N 0)); pi1 (ks (N 1)); 
                       pi1 (ke (N 2))])) (kc (N 3)),
              (ub (c 0 3) pk (bk 5) (x3tt 0 1), TWO)) }_ 2 ^^ 11,
           msg {(c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO)) }_ 2 ^^ 12,
           msg (pi2 (ks (N 0))), msg (pi2 (ks (N 1))), 
           msg (rs (N 9)), msg (rs (N 10)),
           msg
             (pi1 (ks (N 0)),
             (bl
                (comm
                   (V0
                      (f
                         [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                         pi1 (ks (N 0)); pi1 (ks (N 1)); 
                         pi1 (ke (N 2))])) (kc (N 3)))
                (pubkey
                   (f
                      [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                      pi1 (ks (N 0)); pi1 (ks (N 1)); 
                      pi1 (ke (N 2))])) (rb (N 5)),
             sign
               (bl
                  (comm
                     (V0
                        (f
                           [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                           pi1 (ks (N 0)); pi1 (ks (N 1)); 
                           pi1 (ke (N 2))])) (kc (N 3)))
                  (pubkey
                     (f
                        [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                        pi1 (ks (N 0)); pi1 (ks (N 1)); 
                        pi1 (ke (N 2))])) (rb (N 5))) 
               (pi2 (ks (N 0))) (rs (N 9)))),
           msg
             (pi1 (ks (N 1)),
             (bl
                (comm
                   (V1
                      (f
                         [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                         pi1 (ks (N 0)); pi1 (ks (N 1)); 
                         pi1 (ke (N 2))])) (kc (N 4)))
                (pubkey
                   (f
                      [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                      pi1 (ks (N 0)); pi1 (ks (N 1)); 
                      pi1 (ke (N 2))])) (rb (N 6)),
             sign
               (bl
                  (comm
                     (V1
                        (f
                           [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                           pi1 (ks (N 0)); pi1 (ks (N 1)); 
                           pi1 (ke (N 2))])) (kc (N 4)))
                  (pubkey
                     (f
                        [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                        pi1 (ks (N 0)); pi1 (ks (N 1)); 
                        pi1 (ke (N 2))])) (rb (N 6))) 
               (pi2 (ks (N 1))) (rs (N 10)))),
           msg
             (f
                [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
                (pi1 (ks (N 0)),
                (bl
                   (comm
                      (V0
                         (f
                            [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                            pi1 (ks (N 0)); pi1 (ks (N 1)); 
                            pi1 (ke (N 2))])) (kc (N 3)))
                   (pubkey
                      (f
                         [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                         pi1 (ks (N 0)); pi1 (ks (N 1)); 
                         pi1 (ke (N 2))])) (rb (N 5)),
                sign
                  (bl
                     (comm
                        (V0
                           (f
                              [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                              pi1 (ks (N 0)); pi1 (ks (N 1));
                              pi1 (ke (N 2))])) (kc (N 3)))
                     (pubkey
                        (f
                           [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                           pi1 (ks (N 0)); pi1 (ks (N 1)); 
                           pi1 (ke (N 2))])) (rb (N 5))) 
                  (pi2 (ks (N 0))) (rs (N 9))));
                (pi1 (ks (N 1)),
                (bl
                   (comm
                      (V1
                         (f
                            [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                            pi1 (ks (N 0)); pi1 (ks (N 1)); 
                            pi1 (ke (N 2))])) (kc (N 4)))
                   (pubkey
                      (f
                         [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                         pi1 (ks (N 0)); pi1 (ks (N 1)); 
                         pi1 (ke (N 2))])) (rb (N 6)),
                sign
                  (bl
                     (comm
                        (V1
                           (f
                              [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                              pi1 (ks (N 0)); pi1 (ks (N 1));
                              pi1 (ke (N 2))])) (kc (N 4)))
                     (pubkey
                        (f
                           [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                           pi1 (ks (N 0)); pi1 (ks (N 1)); 
                           pi1 (ke (N 2))])) (rb (N 6))) 
                  (pi2 (ks (N 1))) (rs (N 10))))]), 
           msg (x4ttt 0 1), msg (x5t 0 1),
           bol
             (acc
                (comm
                   (V0
                      (f
                         [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                         pi1 (ks (N 0)); pi1 (ks (N 1)); 
                         pi1 (ke (N 2))])) (kc (N 3)))
                (pubkey
                   (f
                      [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                      pi1 (ks (N 0)); pi1 (ks (N 1)); 
                      pi1 (ke (N 2))])) (rb (N 5))
                (f
                   [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                   pi1 (ks (N 0)); pi1 (ks (N 1)); 
                   pi1 (ke (N 2));
                   (pi1 (ks (N 0)),
                   (bl
                      (comm
                         (V0
                            (f
                               [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                               pi1 (ks (N 0)); pi1 (ks (N 1));
                               pi1 (ke (N 2))])) (kc (N 3)))
                      (pubkey
                         (f
                            [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                            pi1 (ks (N 0)); pi1 (ks (N 1)); 
                            pi1 (ke (N 2))])) (rb (N 5)),
                   sign
                     (bl
                        (comm
                           (V0
                              (f
                                 [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                 pi1 (ks (N 0)); pi1 (ks (N 1));
                                 pi1 (ke (N 2))])) 
                           (kc (N 3)))
                        (pubkey
                           (f
                              [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                              pi1 (ks (N 0)); pi1 (ks (N 1));
                              pi1 (ke (N 2))])) (rb (N 5))) 
                     (pi2 (ks (N 0))) (rs (N 9))));
                   (pi1 (ks (N 1)),
                   (bl
                      (comm
                         (V1
                            (f
                               [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                               pi1 (ks (N 0)); pi1 (ks (N 1));
                               pi1 (ke (N 2))])) (kc (N 4)))
                      (pubkey
                         (f
                            [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                            pi1 (ks (N 0)); pi1 (ks (N 1)); 
                            pi1 (ke (N 2))])) (rb (N 6)),
                   sign
                     (bl
                        (comm
                           (V1
                              (f
                                 [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                 pi1 (ks (N 0)); pi1 (ks (N 1));
                                 pi1 (ke (N 2))])) 
                           (kc (N 4)))
                        (pubkey
                           (f
                              [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                              pi1 (ks (N 0)); pi1 (ks (N 1));
                              pi1 (ke (N 2))])) (rb (N 6))) 
                     (pi2 (ks (N 1))) (rs (N 10))))])),
           bol
             (acc
                (comm
                   (V1
                      (f
                         [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                         pi1 (ks (N 0)); pi1 (ks (N 1)); 
                         pi1 (ke (N 2))])) (kc (N 4)))
                (pubkey
                   (f
                      [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                      pi1 (ks (N 0)); pi1 (ks (N 1)); 
                      pi1 (ke (N 2))])) (rb (N 6))
                (f
                   [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                   pi1 (ks (N 0)); pi1 (ks (N 1)); 
                   pi1 (ke (N 2));
                   (pi1 (ks (N 0)),
                   (bl
                      (comm
                         (V0
                            (f
                               [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                               pi1 (ks (N 0)); pi1 (ks (N 1));
                               pi1 (ke (N 2))])) (kc (N 3)))
                      (pubkey
                         (f
                            [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                            pi1 (ks (N 0)); pi1 (ks (N 1)); 
                            pi1 (ke (N 2))])) (rb (N 5)),
                   sign
                     (bl
                        (comm
                           (V0
                              (f
                                 [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                 pi1 (ks (N 0)); pi1 (ks (N 1));
                                 pi1 (ke (N 2))])) 
                           (kc (N 3)))
                        (pubkey
                           (f
                              [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                              pi1 (ks (N 0)); pi1 (ks (N 1));
                              pi1 (ke (N 2))])) (rb (N 5))) 
                     (pi2 (ks (N 0))) (rs (N 9))));
                   (pi1 (ks (N 1)),
                   (bl
                      (comm
                         (V1
                            (f
                               [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                               pi1 (ks (N 0)); pi1 (ks (N 1));
                               pi1 (ke (N 2))])) (kc (N 4)))
                      (pubkey
                         (f
                            [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                            pi1 (ks (N 0)); pi1 (ks (N 1)); 
                            pi1 (ke (N 2))])) (rb (N 6)),
                   sign
                     (bl
                        (comm
                           (V1
                              (f
                                 [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                 pi1 (ks (N 0)); pi1 (ks (N 1));
                                 pi1 (ke (N 2))])) 
                           (kc (N 4)))
                        (pubkey
                           (f
                              [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                              pi1 (ks (N 0)); pi1 (ks (N 1));
                              pi1 (ke (N 2))])) (rb (N 6))) 
                     (pi2 (ks (N 1))) (rs (N 10))))]))] ~ [msg (dec (pi2 (pi2 (x5t 1 0))) (pi2 (ke (N 2)))),
       msg
         (comm
            (V1
               (f
                  [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                  pi1 (ks (N 0)); pi1 (ks (N 1)); 
                  pi1 (ke (N 2))])) (kc (N 3)),
         ub
           (comm
              (V1
                 (f
                    [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                    pi1 (ks (N 0)); pi1 (ks (N 1)); 
                    pi1 (ke (N 2))])) (kc (N 3)))
           (pubkey
              (f
                 [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                 pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
           (rb (N 5))
           (f
              [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
              pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
              (pi1 (ks (N 0)),
              (bl
                 (comm
                    (V1
                       (f
                          [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                          pi1 (ks (N 0)); pi1 (ks (N 1)); 
                          pi1 (ke (N 2))])) (kc (N 3)))
                 (pubkey
                    (f
                       [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                       pi1 (ks (N 0)); pi1 (ks (N 1)); 
                       pi1 (ke (N 2))])) (rb (N 5)),
              sign
                (bl
                   (comm
                      (V1
                         (f
                            [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                            pi1 (ks (N 0)); pi1 (ks (N 1)); 
                            pi1 (ke (N 2))])) (kc (N 3)))
                   (pubkey
                      (f
                         [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                         pi1 (ks (N 0)); pi1 (ks (N 1)); 
                         pi1 (ke (N 2))])) (rb (N 5))) 
                (pi2 (ks (N 0))) (rs (N 9))));
              (pi1 (ks (N 1)),
              (bl
                 (comm
                    (V0
                       (f
                          [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                          pi1 (ks (N 0)); pi1 (ks (N 1)); 
                          pi1 (ke (N 2))])) (kc (N 4)))
                 (pubkey
                    (f
                       [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                       pi1 (ks (N 0)); pi1 (ks (N 1)); 
                       pi1 (ke (N 2))])) (rb (N 6)),
              sign
                (bl
                   (comm
                      (V0
                         (f
                            [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                            pi1 (ks (N 0)); pi1 (ks (N 1)); 
                            pi1 (ke (N 2))])) (kc (N 4)))
                   (pubkey
                      (f
                         [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                         pi1 (ks (N 0)); pi1 (ks (N 1)); 
                         pi1 (ke (N 2))])) (rb (N 6))) 
                (pi2 (ks (N 1))) (rs (N 10))))])),
       msg
         (comm
            (V0
               (f
                  [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                  pi1 (ks (N 0)); pi1 (ks (N 1)); 
                  pi1 (ke (N 2))])) (kc (N 4)),
         ub
           (comm
              (V0
                 (f
                    [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                    pi1 (ks (N 0)); pi1 (ks (N 1)); 
                    pi1 (ke (N 2))])) (kc (N 4)))
           (pubkey
              (f
                 [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                 pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2))]))
           (rb (N 6))
           (f
              [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
              pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
              (pi1 (ks (N 0)),
              (bl
                 (comm
                    (V1
                       (f
                          [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                          pi1 (ks (N 0)); pi1 (ks (N 1)); 
                          pi1 (ke (N 2))])) (kc (N 3)))
                 (pubkey
                    (f
                       [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                       pi1 (ks (N 0)); pi1 (ks (N 1)); 
                       pi1 (ke (N 2))])) (rb (N 5)),
              sign
                (bl
                   (comm
                      (V1
                         (f
                            [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                            pi1 (ks (N 0)); pi1 (ks (N 1)); 
                            pi1 (ke (N 2))])) (kc (N 3)))
                   (pubkey
                      (f
                         [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                         pi1 (ks (N 0)); pi1 (ks (N 1)); 
                         pi1 (ke (N 2))])) (rb (N 5))) 
                (pi2 (ks (N 0))) (rs (N 9))));
              (pi1 (ks (N 1)),
              (bl
                 (comm
                    (V0
                       (f
                          [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                          pi1 (ks (N 0)); pi1 (ks (N 1)); 
                          pi1 (ke (N 2))])) (kc (N 4)))
                 (pubkey
                    (f
                       [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                       pi1 (ks (N 0)); pi1 (ks (N 1)); 
                       pi1 (ke (N 2))])) (rb (N 6)),
              sign
                (bl
                   (comm
                      (V0
                         (f
                            [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                            pi1 (ks (N 0)); pi1 (ks (N 1)); 
                            pi1 (ke (N 2))])) (kc (N 4)))
                   (pubkey
                      (f
                         [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                         pi1 (ks (N 0)); pi1 (ks (N 1)); 
                         pi1 (ke (N 2))])) (rb (N 6))) 
                (pi2 (ks (N 1))) (rs (N 10))))])), 
       msg A, msg B, msg M, msg C1, msg C2, msg C3, 
       msg ONE, msg TWO, msg THREE, msg (pi1 (ks (N 0))),
       msg (pi1 (ks (N 1))), msg (pi1 (ke (N 2))),
       msg
         {(comm
             (V1
                (f
                   [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                   pi1 (ks (N 0)); pi1 (ks (N 1)); 
                   pi1 (ke (N 2))])) (kc (N 3)),
          (ub
             (comm
                (V1
                   (f
                      [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                      pi1 (ks (N 0)); pi1 (ks (N 1)); 
                      pi1 (ke (N 2))])) (kc (N 3)))
             (pubkey
                (f
                   [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                   pi1 (ks (N 0)); pi1 (ks (N 1)); 
                   pi1 (ke (N 2))])) (rb (N 5))
             (f
                [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
                (pi1 (ks (N 0)),
                (bl
                   (comm
                      (V1
                         (f
                            [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                            pi1 (ks (N 0)); pi1 (ks (N 1)); 
                            pi1 (ke (N 2))])) (kc (N 3)))
                   (pubkey
                      (f
                         [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                         pi1 (ks (N 0)); pi1 (ks (N 1)); 
                         pi1 (ke (N 2))])) (rb (N 5)),
                sign
                  (bl
                     (comm
                        (V1
                           (f
                              [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                              pi1 (ks (N 0)); pi1 (ks (N 1));
                              pi1 (ke (N 2))])) (kc (N 3)))
                     (pubkey
                        (f
                           [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                           pi1 (ks (N 0)); pi1 (ks (N 1)); 
                           pi1 (ke (N 2))])) (rb (N 5))) 
                  (pi2 (ks (N 0))) (rs (N 9))));
                (pi1 (ks (N 1)),
                (bl
                   (comm
                      (V0
                         (f
                            [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                            pi1 (ks (N 0)); pi1 (ks (N 1)); 
                            pi1 (ke (N 2))])) (kc (N 4)))
                   (pubkey
                      (f
                         [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                         pi1 (ks (N 0)); pi1 (ks (N 1)); 
                         pi1 (ke (N 2))])) (rb (N 6)),
                sign
                  (bl
                     (comm
                        (V0
                           (f
                              [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                              pi1 (ks (N 0)); pi1 (ks (N 1));
                              pi1 (ke (N 2))])) (kc (N 4)))
                     (pubkey
                        (f
                           [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                           pi1 (ks (N 0)); pi1 (ks (N 1)); 
                           pi1 (ke (N 2))])) (rb (N 6))) 
                  (pi2 (ks (N 1))) (rs (N 10))))]), TWO)) }_ 2 ^^ 11,
       msg {(c 0 4, (ub (c 0 4) pk (bk 6) (x3tt 1 0), TWO)) }_ 2 ^^ 12,
       msg (pi2 (ks (N 0))), msg (pi2 (ks (N 1))), 
       msg (rs (N 9)), msg (rs (N 10)),
       msg
         (pi1 (ks (N 0)),
         (bl
            (comm
               (V1
                  (f
                     [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                     pi1 (ks (N 0)); pi1 (ks (N 1)); 
                     pi1 (ke (N 2))])) (kc (N 3)))
            (pubkey
               (f
                  [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                  pi1 (ks (N 0)); pi1 (ks (N 1)); 
                  pi1 (ke (N 2))])) (rb (N 5)),
         sign
           (bl
              (comm
                 (V1
                    (f
                       [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                       pi1 (ks (N 0)); pi1 (ks (N 1)); 
                       pi1 (ke (N 2))])) (kc (N 3)))
              (pubkey
                 (f
                    [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                    pi1 (ks (N 0)); pi1 (ks (N 1)); 
                    pi1 (ke (N 2))])) (rb (N 5))) 
           (pi2 (ks (N 0))) (rs (N 9)))),
       msg
         (pi1 (ks (N 1)),
         (bl
            (comm
               (V0
                  (f
                     [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                     pi1 (ks (N 0)); pi1 (ks (N 1)); 
                     pi1 (ke (N 2))])) (kc (N 4)))
            (pubkey
               (f
                  [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                  pi1 (ks (N 0)); pi1 (ks (N 1)); 
                  pi1 (ke (N 2))])) (rb (N 6)),
         sign
           (bl
              (comm
                 (V0
                    (f
                       [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                       pi1 (ks (N 0)); pi1 (ks (N 1)); 
                       pi1 (ke (N 2))])) (kc (N 4)))
              (pubkey
                 (f
                    [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                    pi1 (ks (N 0)); pi1 (ks (N 1)); 
                    pi1 (ke (N 2))])) (rb (N 6))) 
           (pi2 (ks (N 1))) (rs (N 10)))),
       msg
         (f
            [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
            pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
            (pi1 (ks (N 0)),
            (bl
               (comm
                  (V1
                     (f
                        [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                        pi1 (ks (N 0)); pi1 (ks (N 1)); 
                        pi1 (ke (N 2))])) (kc (N 3)))
               (pubkey
                  (f
                     [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                     pi1 (ks (N 0)); pi1 (ks (N 1)); 
                     pi1 (ke (N 2))])) (rb (N 5)),
            sign
              (bl
                 (comm
                    (V1
                       (f
                          [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                          pi1 (ks (N 0)); pi1 (ks (N 1)); 
                          pi1 (ke (N 2))])) (kc (N 3)))
                 (pubkey
                    (f
                       [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                       pi1 (ks (N 0)); pi1 (ks (N 1)); 
                       pi1 (ke (N 2))])) (rb (N 5))) 
              (pi2 (ks (N 0))) (rs (N 9))));
            (pi1 (ks (N 1)),
            (bl
               (comm
                  (V0
                     (f
                        [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                        pi1 (ks (N 0)); pi1 (ks (N 1)); 
                        pi1 (ke (N 2))])) (kc (N 4)))
               (pubkey
                  (f
                     [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                     pi1 (ks (N 0)); pi1 (ks (N 1)); 
                     pi1 (ke (N 2))])) (rb (N 6)),
            sign
              (bl
                 (comm
                    (V0
                       (f
                          [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                          pi1 (ks (N 0)); pi1 (ks (N 1)); 
                          pi1 (ke (N 2))])) (kc (N 4)))
                 (pubkey
                    (f
                       [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                       pi1 (ks (N 0)); pi1 (ks (N 1)); 
                       pi1 (ke (N 2))])) (rb (N 6))) 
              (pi2 (ks (N 1))) (rs (N 10))))]),
       msg (x4ttt 1 0),
          msg (x5t 1 0),
       bol
         (acc
            (comm
               (V1
                  (f
                     [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                     pi1 (ks (N 0)); pi1 (ks (N 1)); 
                     pi1 (ke (N 2))])) (kc (N 3)))
            (pubkey
               (f
                  [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                  pi1 (ks (N 0)); pi1 (ks (N 1)); 
                  pi1 (ke (N 2))])) (rb (N 5))
            (f
               [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
               pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
               (pi1 (ks (N 0)),
               (bl
                  (comm
                     (V1
                        (f
                           [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                           pi1 (ks (N 0)); pi1 (ks (N 1)); 
                           pi1 (ke (N 2))])) (kc (N 3)))
                  (pubkey
                     (f
                        [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                        pi1 (ks (N 0)); pi1 (ks (N 1)); 
                        pi1 (ke (N 2))])) (rb (N 5)),
               sign
                 (bl
                    (comm
                       (V1
                          (f
                             [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                             pi1 (ks (N 0)); pi1 (ks (N 1)); 
                             pi1 (ke (N 2))])) (kc (N 3)))
                    (pubkey
                       (f
                          [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                          pi1 (ks (N 0)); pi1 (ks (N 1)); 
                          pi1 (ke (N 2))])) (rb (N 5))) 
                 (pi2 (ks (N 0))) (rs (N 9))));
               (pi1 (ks (N 1)),
               (bl
                  (comm
                     (V0
                        (f
                           [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                           pi1 (ks (N 0)); pi1 (ks (N 1)); 
                           pi1 (ke (N 2))])) (kc (N 4)))
                  (pubkey
                     (f
                        [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                        pi1 (ks (N 0)); pi1 (ks (N 1)); 
                        pi1 (ke (N 2))])) (rb (N 6)),
               sign
                 (bl
                    (comm
                       (V0
                          (f
                             [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                             pi1 (ks (N 0)); pi1 (ks (N 1)); 
                             pi1 (ke (N 2))])) (kc (N 4)))
                    (pubkey
                       (f
                          [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                          pi1 (ks (N 0)); pi1 (ks (N 1)); 
                          pi1 (ke (N 2))])) (rb (N 6))) 
                 (pi2 (ks (N 1))) (rs (N 10))))])),
       bol
         (acc
            (comm
               (V0
                  (f
                     [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                     pi1 (ks (N 0)); pi1 (ks (N 1)); 
                     pi1 (ke (N 2))])) (kc (N 4)))
            (pubkey
               (f
                  [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                  pi1 (ks (N 0)); pi1 (ks (N 1)); 
                  pi1 (ke (N 2))])) (rb (N 6))
            (f
               [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
               pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
               (pi1 (ks (N 0)),
               (bl
                  (comm
                     (V1
                        (f
                           [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                           pi1 (ks (N 0)); pi1 (ks (N 1)); 
                           pi1 (ke (N 2))])) (kc (N 3)))
                  (pubkey
                     (f
                        [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                        pi1 (ks (N 0)); pi1 (ks (N 1)); 
                        pi1 (ke (N 2))])) (rb (N 5)),
               sign
                 (bl
                    (comm
                       (V1
                          (f
                             [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                             pi1 (ks (N 0)); pi1 (ks (N 1)); 
                             pi1 (ke (N 2))])) (kc (N 3)))
                    (pubkey
                       (f
                          [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                          pi1 (ks (N 0)); pi1 (ks (N 1)); 
                          pi1 (ke (N 2))])) (rb (N 5))) 
                 (pi2 (ks (N 0))) (rs (N 9))));
               (pi1 (ks (N 1)),
               (bl
                  (comm
                     (V0
                        (f
                           [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                           pi1 (ks (N 0)); pi1 (ks (N 1)); 
                           pi1 (ke (N 2))])) (kc (N 4)))
                  (pubkey
                     (f
                        [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                        pi1 (ks (N 0)); pi1 (ks (N 1)); 
                        pi1 (ke (N 2))])) (rb (N 6)),
               sign
                 (bl
                    (comm
                       (V0
                          (f
                             [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                             pi1 (ks (N 0)); pi1 (ks (N 1)); 
                             pi1 (ke (N 2))])) (kc (N 4)))
                    (pubkey
                       (f
                          [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                          pi1 (ks (N 0)); pi1 (ks (N 1)); 
                          pi1 (ke (N 2))])) (rb (N 6))) 
                 (pi2 (ks (N 1))) (rs (N 10))))]))]).


apply EQI_trans with (ml2:= [msg
           (dec
              (pi2
                 (pi2
                    (f
                       [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                       pi1 (ks (N 0)); pi1 (ks (N 1)); 
                       pi1 (ke (N 2));
                       (pi1 (ks (N 0)),
                       (bl
                          (comm
                             (V1
                                (f
                                   [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                   pi1 (ks (N 0)); 
                                   pi1 (ks (N 1)); 
                                   pi1 (ke (N 2))])) 
                             (kc (N 3)))
                          (pubkey
                             (f
                                [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                pi1 (ks (N 0)); pi1 (ks (N 1));
                                pi1 (ke (N 2))])) 
                          (rb (N 5)),
                       sign
                         (bl
                            (comm
                               (V1
                                  (f
                                     [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                     pi1 (ks (N 0)); 
                                     pi1 (ks (N 1)); 
                                     pi1 (ke (N 2))])) 
                               (kc (N 3)))
                            (pubkey
                               (f
                                  [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                  pi1 (ks (N 0)); 
                                  pi1 (ks (N 1)); 
                                  pi1 (ke (N 2))])) 
                            (rb (N 5))) (pi2 (ks (N 0))) 
                         (rs (N 9))));
                       (pi1 (ks (N 1)),
                       (bl
                          (comm
                             (V0
                                (f
                                   [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                   pi1 (ks (N 0)); 
                                   pi1 (ks (N 1)); 
                                   pi1 (ke (N 2))])) 
                             (kc (N 4)))
                          (pubkey
                             (f
                                [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                pi1 (ks (N 0)); pi1 (ks (N 1));
                                pi1 (ke (N 2))])) 
                          (rb (N 6)),
                       sign
                         (bl
                            (comm
                               (V0
                                  (f
                                     [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                     pi1 (ks (N 0)); 
                                     pi1 (ks (N 1)); 
                                     pi1 (ke (N 2))])) 
                               (kc (N 4)))
                            (pubkey
                               (f
                                  [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                  pi1 (ks (N 0)); 
                                  pi1 (ks (N 1)); 
                                  pi1 (ke (N 2))])) 
                            (rb (N 6))) (pi2 (ks (N 1))) 
                         (rs (N 10))));
                       {z
                          (comm
                             (V0
                                (f
                                   [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                   pi1 (ks (N 0)); 
                                   pi1 (ks (N 1)); 
                                   pi1 (ke (N 2))])) 
                             (kc (N 3)),
                          (ub
                             (comm
                                (V0
                                   (f
                                      [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                      pi1 (ks (N 0)); 
                                      pi1 (ks (N 1)); 
                                      pi1 (ke (N 2))])) 
                                (kc (N 3)))
                             (pubkey
                                (f
                                   [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                   pi1 (ks (N 0)); 
                                   pi1 (ks (N 1)); 
                                   pi1 (ke (N 2))])) 
                             (rb (N 5))
                             (f
                                [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                pi1 (ks (N 0)); pi1 (ks (N 1));
                                pi1 (ke (N 2));
                                (pi1 (ks (N 0)),
                                (bl
                                   (comm
                                      (V1
                                         (f
                                            [A; B; M; C1; C2; C3; ONE; TWO;
                                            THREE; 
                                            vk 0; 
                                            vk 1; 
                                            pke 2])) 
                                      (kc (N 3))) 
                                   (pubkey x1) (r 5),
                                sign
                                  (bl
                                     (comm
                                        (V1
                                           (f
                                              [A; B; M; C1; C2; C3; ONE;
                                              TWO; THREE; 
                                              vk 0; 
                                              vk 1; 
                                              pke 2])) 
                                        (kc (N 3))) 
                                     (pubkey x1) (r 5)) 
                                  (pi2 (ks (N 0))) 
                                  (rs (N 9))));
                                (pi1 (ks (N 1)),
                                (bl
                                   (comm
                                      (V0
                                         (f
                                            [A; B; M; C1; C2; C3; ONE; TWO;
                                            THREE; 
                                            pi1 (ks (N 0)); 
                                            pi1 (ks (N 1)); 
                                            pi1 (ke (N 2))])) 
                                      (kc (N 4)))
                                   (pubkey
                                      (f
                                         [A; B; M; C1; C2; C3; ONE; TWO;
                                         THREE; pi1 (ks (N 0));
                                         pi1 (ks (N 1)); 
                                         pi1 (ke (N 2))])) 
                                   (rb (N 6)),
                                sign
                                  (bl
                                     (comm
                                        (V0
                                           (f
                                              [A; B; M; C1; C2; C3; ONE;
                                              TWO; THREE; 
                                              pi1 (ks (N 0));
                                              pi1 (ks (N 1));
                                              pi1 (ke (N 2))])) 
                                        (kc (N 4)))
                                     (pubkey
                                        (f
                                           [A; B; M; C1; C2; C3; ONE; TWO;
                                           THREE; 
                                           pi1 (ks (N 0)); 
                                           pi1 (ks (N 1)); 
                                           pi1 (ke (N 2))])) 
                                     (rb (N 6))) (pi2 (ks (N 1)))
                                  (rs (N 10))))]), TWO)) }_ 2 ^^ 13;
                       {z (c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 1 0), TWO))
                       }_ 2 ^^ 14]))) (pi2 (ke (N 2)))),
        msg
          (comm
             (V1
                (f
                   [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                   pi1 (ks (N 0)); pi1 (ks (N 1)); 
                   pi1 (ke (N 2))])) (kc (N 3)),
          ub
            (comm
               (V1
                  (f
                     [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                     pi1 (ks (N 0)); pi1 (ks (N 1)); 
                     pi1 (ke (N 2))])) (kc (N 3)))
            (pubkey
               (f
                  [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                  pi1 (ks (N 0)); pi1 (ks (N 1)); 
                  pi1 (ke (N 2))])) (rb (N 5))
            (f
               [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
               pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
               (pi1 (ks (N 0)),
               (bl
                  (comm
                     (V1
                        (f
                           [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                           pi1 (ks (N 0)); pi1 (ks (N 1)); 
                           pi1 (ke (N 2))])) (kc (N 3)))
                  (pubkey
                     (f
                        [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                        pi1 (ks (N 0)); pi1 (ks (N 1)); 
                        pi1 (ke (N 2))])) (rb (N 5)),
               sign
                 (bl
                    (comm
                       (V1
                          (f
                             [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                             pi1 (ks (N 0)); pi1 (ks (N 1)); 
                             pi1 (ke (N 2))])) (kc (N 3)))
                    (pubkey
                       (f
                          [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                          pi1 (ks (N 0)); pi1 (ks (N 1)); 
                          pi1 (ke (N 2))])) (rb (N 5))) 
                 (pi2 (ks (N 0))) (rs (N 9))));
               (pi1 (ks (N 1)),
               (bl
                  (comm
                     (V0
                        (f
                           [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                           pi1 (ks (N 0)); pi1 (ks (N 1)); 
                           pi1 (ke (N 2))])) (kc (N 4)))
                  (pubkey
                     (f
                        [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                        pi1 (ks (N 0)); pi1 (ks (N 1)); 
                        pi1 (ke (N 2))])) (rb (N 6)),
               sign
                 (bl
                    (comm
                       (V0
                          (f
                             [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                             pi1 (ks (N 0)); pi1 (ks (N 1)); 
                             pi1 (ke (N 2))])) (kc (N 4)))
                    (pubkey
                       (f
                          [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                          pi1 (ks (N 0)); pi1 (ks (N 1)); 
                          pi1 (ke (N 2))])) (rb (N 6))) 
                 (pi2 (ks (N 1))) (rs (N 10))))])),
        msg
          (comm
             (V0
                (f
                   [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                   pi1 (ks (N 0)); pi1 (ks (N 1)); 
                   pi1 (ke (N 2))])) (kc (N 4)),
          ub
            (comm
               (V0
                  (f
                     [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                     pi1 (ks (N 0)); pi1 (ks (N 1)); 
                     pi1 (ke (N 2))])) (kc (N 4)))
            (pubkey
               (f
                  [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                  pi1 (ks (N 0)); pi1 (ks (N 1)); 
                  pi1 (ke (N 2))])) (rb (N 6))
            (f
               [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
               pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
               (pi1 (ks (N 0)),
               (bl
                  (comm
                     (V1
                        (f
                           [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                           pi1 (ks (N 0)); pi1 (ks (N 1)); 
                           pi1 (ke (N 2))])) (kc (N 3)))
                  (pubkey
                     (f
                        [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                        pi1 (ks (N 0)); pi1 (ks (N 1)); 
                        pi1 (ke (N 2))])) (rb (N 5)),
               sign
                 (bl
                    (comm
                       (V1
                          (f
                             [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                             pi1 (ks (N 0)); pi1 (ks (N 1)); 
                             pi1 (ke (N 2))])) (kc (N 3)))
                    (pubkey
                       (f
                          [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                          pi1 (ks (N 0)); pi1 (ks (N 1)); 
                          pi1 (ke (N 2))])) (rb (N 5))) 
                 (pi2 (ks (N 0))) (rs (N 9))));
               (pi1 (ks (N 1)),
               (bl
                  (comm
                     (V0
                        (f
                           [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                           pi1 (ks (N 0)); pi1 (ks (N 1)); 
                           pi1 (ke (N 2))])) (kc (N 4)))
                  (pubkey
                     (f
                        [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                        pi1 (ks (N 0)); pi1 (ks (N 1)); 
                        pi1 (ke (N 2))])) (rb (N 6)),
               sign
                 (bl
                    (comm
                       (V0
                          (f
                             [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                             pi1 (ks (N 0)); pi1 (ks (N 1)); 
                             pi1 (ke (N 2))])) (kc (N 4)))
                    (pubkey
                       (f
                          [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                          pi1 (ks (N 0)); pi1 (ks (N 1)); 
                          pi1 (ke (N 2))])) (rb (N 6))) 
                 (pi2 (ks (N 1))) (rs (N 10))))])), 
        msg A, msg B, msg M, msg C1, msg C2, msg C3, 
        msg ONE, msg TWO, msg THREE, msg (pi1 (ks (N 0))),
        msg (pi1 (ks (N 1))), msg (pi1 (ke (N 2))),
        msg
          {z
             (comm
                (V0
                   (f
                      [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                      pi1 (ks (N 0)); pi1 (ks (N 1)); 
                      pi1 (ke (N 2))])) (kc (N 3)),
             (ub
                (comm
                   (V0
                      (f
                         [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                         pi1 (ks (N 0)); pi1 (ks (N 1)); 
                         pi1 (ke (N 2))])) (kc (N 3)))
                (pubkey
                   (f
                      [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                      pi1 (ks (N 0)); pi1 (ks (N 1)); 
                      pi1 (ke (N 2))])) (rb (N 5))
                (f
                   [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                   pi1 (ks (N 0)); pi1 (ks (N 1)); 
                   pi1 (ke (N 2));
                   (pi1 (ks (N 0)),
                   (bl
                      (comm
                         (V1
                            (f
                               [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                               vk 0; vk 1; pke 2])) 
                         (kc (N 3))) (pubkey x1) (r 5),
                   sign
                     (bl
                        (comm
                           (V1
                              (f
                                 [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                 vk 0; vk 1; pke 2])) 
                           (kc (N 3))) (pubkey x1) 
                        (r 5)) (pi2 (ks (N 0))) (rs (N 9))));
                   (pi1 (ks (N 1)),
                   (bl
                      (comm
                         (V0
                            (f
                               [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                               pi1 (ks (N 0)); pi1 (ks (N 1));
                               pi1 (ke (N 2))])) (kc (N 4)))
                      (pubkey
                         (f
                            [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                            pi1 (ks (N 0)); pi1 (ks (N 1)); 
                            pi1 (ke (N 2))])) (rb (N 6)),
                   sign
                     (bl
                        (comm
                           (V0
                              (f
                                 [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                 pi1 (ks (N 0)); pi1 (ks (N 1));
                                 pi1 (ke (N 2))])) 
                           (kc (N 4)))
                        (pubkey
                           (f
                              [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                              pi1 (ks (N 0)); pi1 (ks (N 1));
                              pi1 (ke (N 2))])) (rb (N 6))) 
                     (pi2 (ks (N 1))) (rs (N 10))))]), TWO)) }_ 2 ^^ 13,
        msg {z (c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 1 0), TWO)) }_ 2 ^^ 14,
        msg (pi2 (ks (N 0))), msg (pi2 (ks (N 1))), 
        msg (rs (N 9)), msg (rs (N 10)),
        msg
          (pi1 (ks (N 0)),
          (bl
             (comm
                (V1
                   (f
                      [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                      pi1 (ks (N 0)); pi1 (ks (N 1)); 
                      pi1 (ke (N 2))])) (kc (N 3)))
             (pubkey
                (f
                   [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                   pi1 (ks (N 0)); pi1 (ks (N 1)); 
                   pi1 (ke (N 2))])) (rb (N 5)),
          sign
            (bl
               (comm
                  (V1
                     (f
                        [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                        pi1 (ks (N 0)); pi1 (ks (N 1)); 
                        pi1 (ke (N 2))])) (kc (N 3)))
               (pubkey
                  (f
                     [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                     pi1 (ks (N 0)); pi1 (ks (N 1)); 
                     pi1 (ke (N 2))])) (rb (N 5))) 
            (pi2 (ks (N 0))) (rs (N 9)))),
        msg
          (pi1 (ks (N 1)),
          (bl
             (comm
                (V0
                   (f
                      [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                      pi1 (ks (N 0)); pi1 (ks (N 1)); 
                      pi1 (ke (N 2))])) (kc (N 4)))
             (pubkey
                (f
                   [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                   pi1 (ks (N 0)); pi1 (ks (N 1)); 
                   pi1 (ke (N 2))])) (rb (N 6)),
          sign
            (bl
               (comm
                  (V0
                     (f
                        [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                        pi1 (ks (N 0)); pi1 (ks (N 1)); 
                        pi1 (ke (N 2))])) (kc (N 4)))
               (pubkey
                  (f
                     [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                     pi1 (ks (N 0)); pi1 (ks (N 1)); 
                     pi1 (ke (N 2))])) (rb (N 6))) 
            (pi2 (ks (N 1))) (rs (N 10)))),
        msg
          (f
             [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
             pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
             (pi1 (ks (N 0)),
             (bl
                (comm
                   (V1
                      (f
                         [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                         pi1 (ks (N 0)); pi1 (ks (N 1)); 
                         pi1 (ke (N 2))])) (kc (N 3)))
                (pubkey
                   (f
                      [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                      pi1 (ks (N 0)); pi1 (ks (N 1)); 
                      pi1 (ke (N 2))])) (rb (N 5)),
             sign
               (bl
                  (comm
                     (V1
                        (f
                           [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                           pi1 (ks (N 0)); pi1 (ks (N 1)); 
                           pi1 (ke (N 2))])) (kc (N 3)))
                  (pubkey
                     (f
                        [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                        pi1 (ks (N 0)); pi1 (ks (N 1)); 
                        pi1 (ke (N 2))])) (rb (N 5))) 
               (pi2 (ks (N 0))) (rs (N 9))));
             (pi1 (ks (N 1)),
             (bl
                (comm
                   (V0
                      (f
                         [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                         pi1 (ks (N 0)); pi1 (ks (N 1)); 
                         pi1 (ke (N 2))])) (kc (N 4)))
                (pubkey
                   (f
                      [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                      pi1 (ks (N 0)); pi1 (ks (N 1)); 
                      pi1 (ke (N 2))])) (rb (N 6)),
             sign
               (bl
                  (comm
                     (V0
                        (f
                           [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                           pi1 (ks (N 0)); pi1 (ks (N 1)); 
                           pi1 (ke (N 2))])) (kc (N 4)))
                  (pubkey
                     (f
                        [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                        pi1 (ks (N 0)); pi1 (ks (N 1)); 
                        pi1 (ke (N 2))])) (rb (N 6))) 
               (pi2 (ks (N 1))) (rs (N 10))))]),
        msg
          (f
             [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
             pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
             (pi1 (ks (N 0)),
             (bl
                (comm
                   (V1
                      (f
                         [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                         pi1 (ks (N 0)); pi1 (ks (N 1)); 
                         pi1 (ke (N 2))])) (kc (N 3)))
                (pubkey
                   (f
                      [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                      pi1 (ks (N 0)); pi1 (ks (N 1)); 
                      pi1 (ke (N 2))])) (rb (N 5)),
             sign
               (bl
                  (comm
                     (V1
                        (f
                           [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                           pi1 (ks (N 0)); pi1 (ks (N 1)); 
                           pi1 (ke (N 2))])) (kc (N 3)))
                  (pubkey
                     (f
                        [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                        pi1 (ks (N 0)); pi1 (ks (N 1)); 
                        pi1 (ke (N 2))])) (rb (N 5))) 
               (pi2 (ks (N 0))) (rs (N 9))));
             (pi1 (ks (N 1)),
             (bl
                (comm
                   (V0
                      (f
                         [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                         pi1 (ks (N 0)); pi1 (ks (N 1)); 
                         pi1 (ke (N 2))])) (kc (N 4)))
                (pubkey
                   (f
                      [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                      pi1 (ks (N 0)); pi1 (ks (N 1)); 
                      pi1 (ke (N 2))])) (rb (N 6)),
             sign
               (bl
                  (comm
                     (V0
                        (f
                           [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                           pi1 (ks (N 0)); pi1 (ks (N 1)); 
                           pi1 (ke (N 2))])) (kc (N 4)))
                  (pubkey
                     (f
                        [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                        pi1 (ks (N 0)); pi1 (ks (N 1)); 
                        pi1 (ke (N 2))])) (rb (N 6))) 
               (pi2 (ks (N 1))) (rs (N 10))));
             {z
                (comm
                   (V0
                      (f
                         [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                         pi1 (ks (N 0)); pi1 (ks (N 1)); 
                         pi1 (ke (N 2))])) (kc (N 3)),
                (ub
                   (comm
                      (V0
                         (f
                            [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                            pi1 (ks (N 0)); pi1 (ks (N 1)); 
                            pi1 (ke (N 2))])) (kc (N 3)))
                   (pubkey
                      (f
                         [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                         pi1 (ks (N 0)); pi1 (ks (N 1)); 
                         pi1 (ke (N 2))])) (rb (N 5))
                   (f
                      [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                      pi1 (ks (N 0)); pi1 (ks (N 1)); 
                      pi1 (ke (N 2));
                      (pi1 (ks (N 0)),
                      (bl
                         (comm
                            (V1
                               (f
                                  [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                  vk 0; vk 1; pke 2])) 
                            (kc (N 3))) (pubkey x1) 
                         (r 5),
                      sign
                        (bl
                           (comm
                              (V1
                                 (f
                                    [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                    vk 0; vk 1; pke 2])) 
                              (kc (N 3))) (pubkey x1) 
                           (r 5)) (pi2 (ks (N 0))) 
                        (rs (N 9))));
                      (pi1 (ks (N 1)),
                      (bl
                         (comm
                            (V0
                               (f
                                  [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                  pi1 (ks (N 0)); 
                                  pi1 (ks (N 1)); 
                                  pi1 (ke (N 2))])) 
                            (kc (N 4)))
                         (pubkey
                            (f
                               [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                               pi1 (ks (N 0)); pi1 (ks (N 1));
                               pi1 (ke (N 2))])) (rb (N 6)),
                      sign
                        (bl
                           (comm
                              (V0
                                 (f
                                    [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                    pi1 (ks (N 0)); 
                                    pi1 (ks (N 1)); 
                                    pi1 (ke (N 2))])) 
                              (kc (N 4)))
                           (pubkey
                              (f
                                 [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                 pi1 (ks (N 0)); pi1 (ks (N 1));
                                 pi1 (ke (N 2))])) 
                           (rb (N 6))) (pi2 (ks (N 1))) 
                        (rs (N 10))))]), TWO)) }_ 2 ^^ 13]),
        msg
          (f
             [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
             pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
             (pi1 (ks (N 0)),
             (bl
                (comm
                   (V1
                      (f
                         [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                         pi1 (ks (N 0)); pi1 (ks (N 1)); 
                         pi1 (ke (N 2))])) (kc (N 3)))
                (pubkey
                   (f
                      [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                      pi1 (ks (N 0)); pi1 (ks (N 1)); 
                      pi1 (ke (N 2))])) (rb (N 5)),
             sign
               (bl
                  (comm
                     (V1
                        (f
                           [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                           pi1 (ks (N 0)); pi1 (ks (N 1)); 
                           pi1 (ke (N 2))])) (kc (N 3)))
                  (pubkey
                     (f
                        [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                        pi1 (ks (N 0)); pi1 (ks (N 1)); 
                        pi1 (ke (N 2))])) (rb (N 5))) 
               (pi2 (ks (N 0))) (rs (N 9))));
             (pi1 (ks (N 1)),
             (bl
                (comm
                   (V0
                      (f
                         [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                         pi1 (ks (N 0)); pi1 (ks (N 1)); 
                         pi1 (ke (N 2))])) (kc (N 4)))
                (pubkey
                   (f
                      [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                      pi1 (ks (N 0)); pi1 (ks (N 1)); 
                      pi1 (ke (N 2))])) (rb (N 6)),
             sign
               (bl
                  (comm
                     (V0
                        (f
                           [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                           pi1 (ks (N 0)); pi1 (ks (N 1)); 
                           pi1 (ke (N 2))])) (kc (N 4)))
                  (pubkey
                     (f
                        [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                        pi1 (ks (N 0)); pi1 (ks (N 1)); 
                        pi1 (ke (N 2))])) (rb (N 6))) 
               (pi2 (ks (N 1))) (rs (N 10))));
             {z
                (comm
                   (V0
                      (f
                         [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                         pi1 (ks (N 0)); pi1 (ks (N 1)); 
                         pi1 (ke (N 2))])) (kc (N 3)),
                (ub
                   (comm
                      (V0
                         (f
                            [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                            pi1 (ks (N 0)); pi1 (ks (N 1)); 
                            pi1 (ke (N 2))])) (kc (N 3)))
                   (pubkey
                      (f
                         [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                         pi1 (ks (N 0)); pi1 (ks (N 1)); 
                         pi1 (ke (N 2))])) (rb (N 5))
                   (f
                      [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                      pi1 (ks (N 0)); pi1 (ks (N 1)); 
                      pi1 (ke (N 2));
                      (pi1 (ks (N 0)),
                      (bl
                         (comm
                            (V1
                               (f
                                  [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                  vk 0; vk 1; pke 2])) 
                            (kc (N 3))) (pubkey x1) 
                         (r 5),
                      sign
                        (bl
                           (comm
                              (V1
                                 (f
                                    [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                    vk 0; vk 1; pke 2])) 
                              (kc (N 3))) (pubkey x1) 
                           (r 5)) (pi2 (ks (N 0))) 
                        (rs (N 9))));
                      (pi1 (ks (N 1)),
                      (bl
                         (comm
                            (V0
                               (f
                                  [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                  pi1 (ks (N 0)); 
                                  pi1 (ks (N 1)); 
                                  pi1 (ke (N 2))])) 
                            (kc (N 4)))
                         (pubkey
                            (f
                               [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                               pi1 (ks (N 0)); pi1 (ks (N 1));
                               pi1 (ke (N 2))])) (rb (N 6)),
                      sign
                        (bl
                           (comm
                              (V0
                                 (f
                                    [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                    pi1 (ks (N 0)); 
                                    pi1 (ks (N 1)); 
                                    pi1 (ke (N 2))])) 
                              (kc (N 4)))
                           (pubkey
                              (f
                                 [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                                 pi1 (ks (N 0)); pi1 (ks (N 1));
                                 pi1 (ke (N 2))])) 
                           (rb (N 6))) (pi2 (ks (N 1))) 
                        (rs (N 10))))]), TWO)) }_ 2 ^^ 13;
             {z (c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 1 0), TWO)) }_ 2 ^^ 14]),
        bol
          (acc
             (comm
                (V1
                   (f
                      [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                      pi1 (ks (N 0)); pi1 (ks (N 1)); 
                      pi1 (ke (N 2))])) (kc (N 3)))
             (pubkey
                (f
                   [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                   pi1 (ks (N 0)); pi1 (ks (N 1)); 
                   pi1 (ke (N 2))])) (rb (N 5))
             (f
                [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
                (pi1 (ks (N 0)),
                (bl
                   (comm
                      (V1
                         (f
                            [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                            pi1 (ks (N 0)); pi1 (ks (N 1)); 
                            pi1 (ke (N 2))])) (kc (N 3)))
                   (pubkey
                      (f
                         [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                         pi1 (ks (N 0)); pi1 (ks (N 1)); 
                         pi1 (ke (N 2))])) (rb (N 5)),
                sign
                  (bl
                     (comm
                        (V1
                           (f
                              [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                              pi1 (ks (N 0)); pi1 (ks (N 1));
                              pi1 (ke (N 2))])) (kc (N 3)))
                     (pubkey
                        (f
                           [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                           pi1 (ks (N 0)); pi1 (ks (N 1)); 
                           pi1 (ke (N 2))])) (rb (N 5))) 
                  (pi2 (ks (N 0))) (rs (N 9))));
                (pi1 (ks (N 1)),
                (bl
                   (comm
                      (V0
                         (f
                            [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                            pi1 (ks (N 0)); pi1 (ks (N 1)); 
                            pi1 (ke (N 2))])) (kc (N 4)))
                   (pubkey
                      (f
                         [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                         pi1 (ks (N 0)); pi1 (ks (N 1)); 
                         pi1 (ke (N 2))])) (rb (N 6)),
                sign
                  (bl
                     (comm
                        (V0
                           (f
                              [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                              pi1 (ks (N 0)); pi1 (ks (N 1));
                              pi1 (ke (N 2))])) (kc (N 4)))
                     (pubkey
                        (f
                           [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                           pi1 (ks (N 0)); pi1 (ks (N 1)); 
                           pi1 (ke (N 2))])) (rb (N 6))) 
                  (pi2 (ks (N 1))) (rs (N 10))))])),
        bol
          (acc
             (comm
                (V0
                   (f
                      [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                      pi1 (ks (N 0)); pi1 (ks (N 1)); 
                      pi1 (ke (N 2))])) (kc (N 4)))
             (pubkey
                (f
                   [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                   pi1 (ks (N 0)); pi1 (ks (N 1)); 
                   pi1 (ke (N 2))])) (rb (N 6))
             (f
                [A; B; M; C1; C2; C3; ONE; TWO; THREE; 
                pi1 (ks (N 0)); pi1 (ks (N 1)); pi1 (ke (N 2));
                (pi1 (ks (N 0)),
                (bl
                   (comm
                      (V1
                         (f
                            [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                            pi1 (ks (N 0)); pi1 (ks (N 1)); 
                            pi1 (ke (N 2))])) (kc (N 3)))
                   (pubkey
                      (f
                         [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                         pi1 (ks (N 0)); pi1 (ks (N 1)); 
                         pi1 (ke (N 2))])) (rb (N 5)),
                sign
                  (bl
                     (comm
                        (V1
                           (f
                              [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                              pi1 (ks (N 0)); pi1 (ks (N 1));
                              pi1 (ke (N 2))])) (kc (N 3)))
                     (pubkey
                        (f
                           [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                           pi1 (ks (N 0)); pi1 (ks (N 1)); 
                           pi1 (ke (N 2))])) (rb (N 5))) 
                  (pi2 (ks (N 0))) (rs (N 9))));
                (pi1 (ks (N 1)),
                (bl
                   (comm
                      (V0
                         (f
                            [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                            pi1 (ks (N 0)); pi1 (ks (N 1)); 
                            pi1 (ke (N 2))])) (kc (N 4)))
                   (pubkey
                      (f
                         [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                         pi1 (ks (N 0)); pi1 (ks (N 1)); 
                         pi1 (ke (N 2))])) (rb (N 6)),
                sign
                  (bl
                     (comm
                        (V0
                           (f
                              [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                              pi1 (ks (N 0)); pi1 (ks (N 1));
                              pi1 (ke (N 2))])) (kc (N 4)))
                     (pubkey
                        (f
                           [A; B; M; C1; C2; C3; ONE; TWO; THREE;
                           pi1 (ks (N 0)); pi1 (ks (N 1)); 
                           pi1 (ke (N 2))])) (rb (N 6))) 
                  (pi2 (ks (N 1))) (rs (N 10))))]))]).
apply ftran.
apply H1; try split; auto. simpl.
clear ftran.
clear H1.

unfold theta.
unfold vcheck. unfold tr.
 restrsublis H; simpl;auto.
reflexivity.
repeat try auto. reflexivity.
reflexivity.
reflexivity.
Qed.























(** Indistinguishability proof of shuffling step *)
Theorem frame5ind: (phi5 0 1) ~ (phi5 1 0).
Proof.  unfold phi5, phi4, phi3, phi2, phi1. simpl. unfold t1, t2, t3, t4, t4s.
        apply IFBRANCH_M5 with (ml1:= phi0) (ml2:= phi0). unfold Avote. 
        apply IFBRANCH_M4 with (ml1:= phi0 ++ [ bol (theta x1 A), msg (tr 0 0 3 5 9)]) (ml2:= phi0 ++ [bol (theta x1 A), msg (tr 0 1 3 5 9)]).
        apply IFBRANCH_M3 with (ml1:= phi0 ++ [ bol (theta x1 A), msg (tr 0 0 3 5 9), bol (theta (x2t 0) B), msg (tr 1 1 4 6 10)]) (ml2:= phi0 ++ [bol (theta x1 A), msg (tr 0 1 3 5 9), bol (theta (x2t 1) B), msg (tr 1 0 4 6 10)]).

        apply IFBRANCH_M3 with (ml1:= phi0 ++ [ bol (theta x1 A), msg (tr 0 0 3 5 9), bol (theta (x2t 0) B), msg (tr 1 1 4 6 10), bol (to (x3tt 0 1)) #? A]) (ml2:= phi0 ++ [bol (theta x1 A), msg (tr 0 1 3 5 9), bol (theta (x2t 1) B), msg (tr 1 0 4 6 10), bol (to (x3tt 1 0)) #? A]).

        apply IFBRANCH_M2 with (ml1:= phi0 ++ [ bol (theta x1 A), msg (tr 0 0 3 5 9), bol (theta (x2t 0) B), msg (tr 1 1 4 6 10), bol (to (x3tt 0 1)) #? A, bol (acpt 0 3 5 (x3tt 0 1)), msg (e 0 3 5 (x3tt 0 1) TWO 11)]) (ml2:= phi0 ++ [bol (theta x1 A), msg (tr 0 1 3 5 9), bol (theta (x2t 1) B), msg (tr 1 0 4 6 10), bol (to (x3tt 1 0)) #? A, bol (acpt 1 3 5 (x3tt 1 0)), msg (e 1 3 5 (x3tt 1 0) TWO 11)]).
        apply IFBRANCH_M2 with (ml1:= phi0 ++ [ bol (theta x1 A), msg (tr 0 0 3 5 9), bol (theta (x2t 0) B), msg (tr 1 1 4 6 10), bol (to (x3tt 0 1)) #? A, bol (acpt 0 3 5 (x3tt 0 1)), msg (e 0 3 5 (x3tt 0 1) TWO 11), bol (to (x4ttt 0 1)) #? B]) (ml2:= phi0 ++ [bol (theta x1 A), msg (tr 0 1 3 5 9), bol (theta (x2t 1) B), msg (tr 1 0 4 6 10), bol (to (x3tt 1 0)) #? A, bol (acpt 1 3 5 (x3tt 1 0)), msg (e 1 3 5 (x3tt 1 0) TWO 11), bol (to (x4ttt 1 0)) #? B]). simpl. unfold t5, mchecks, strm.

        apply IFBRANCH_M1 with (ml1:= phi0 ++ [ bol (theta x1 A), msg (tr 0 0 3 5 9), bol (theta (x2t 0) B), msg (tr 1 1 4 6 10), bol (to (x3tt 0 1)) #? A, bol (acpt 0 3 5 (x3tt 0 1)), msg (e 0 3 5 (x3tt 0 1) TWO 11), bol (to (x4ttt 0 1)) #? B, bol (acpt 1 4 6 (x3tt 0 1)),
   msg (e 1 4 6 (x3tt 0 1) TWO 12)]) (ml2:= phi0 ++ [bol (theta x1 A), msg (tr 0 1 3 5 9), bol (theta (x2t 1) B), msg (tr 1 0 4 6 10), bol (to (x3tt 1 0)) #? A, bol (acpt 1 3 5 (x3tt 1 0)), msg (e 1 3 5 (x3tt 1 0) TWO 11), bol (to (x4ttt 1 0)) #? B, bol (acpt 0 4 6 (x3tt 1 0)),
                                                     msg (e 0 4 6 (x3tt 1 0) TWO 12)]). simpl.
        unfold p, e, d, negb, pchecks, dist. 
        pose proof(tempax (tau 1 (x5t 0 1)) 2 11 12 (c 0 3, (ub (c 0 3) pk (bk 5) (x3tt 0 1), TWO)) (c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO))) as tau1.
        pose proof(tempax (tau 2 (x5t 0 1)) 2 11 12 (c 0 3, (ub (c 0 3) pk (bk 5) (x3tt 0 1), TWO)) (c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO))) as tau2.
        pose proof(tempax (tau 3 (x5t 0 1)) 2 11 12 (c 0 3, (ub (c 0 3) pk (bk 5) (x3tt 0 1), TWO)) (c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO))) as tau3. repeat unfold d, dist, p, negb, pchecks.  rewrite tau1, tau2, tau3.


pose proof(tempax (tau 1 (x5t 1 0)) 2 11 12 (c 1 3, (ub (c 1 3) pk (bk 5) (x3tt 1 0), TWO)) (c 0 4, (ub (c 0 4) pk (bk 6) (x3tt 1 0), TWO))) as tau1'.
        pose proof(tempax (tau 2 (x5t 1 0)) 2 11 12 (c 1 3, (ub (c 1 3) pk (bk 5) (x3tt 1 0), TWO)) (c 0 4, (ub (c 0 4) pk (bk 6) (x3tt 1 0), TWO))) as tau2'.
                pose proof(tempax (tau 3 (x5t 1 0)) 2 11 12 (c 1 3, (ub (c 1 3) pk (bk 5) (x3tt 1 0), TWO)) (c 0 4, (ub (c 0 4) pk (bk 6) (x3tt 1 0), TWO))) as tau3'.
Admitted.
 