(************************************************************************)
(* Copyright (c) 2017-2018, Ajay Kumar Eeralla <ae266@mail.missouri.edu>*)     
(************************************************************************)
Require Export auth.

Definition Phi1 (n:nat) := phi0 ++ [msg (b n 3 5)].
Definition Phi2 (n n':nat):= (Phi1 n) ++ [msg (b n' 4 6)].
(** abbreviations *)

Definition tau n (m:message) := match n, m with
                                | 1, m => (pi1 m) 
                                | 2, m => (pi1 (pi2 m))
                                | 3, m => (pi2 (pi2 m))
                                | _, _ => O
                                end.
Definition d n x := (dec (tau n x) (ske 2)).
Definition pvchecks x := ((pi2 (d 1 x)) #? TWO) & ((pi2 (d 2 x)) #? TWO) & ((pi2 (d 3 x)) #? TWO).
Definition pochecks x := ((tau 3 (d 1 x)) #? THREE) & ((tau 3 (d 2 x)) #? THREE) & ((tau 3 (d 3 x)) #? THREE).

Definition dist x := !((d 1 x) #? (d 2 x)) & !((d 1 x) #? (d 3 x))& ! ((d 2 x) #? (d 3 x)). 
Definition isin (x y:message):Bool := (x #? (tau 1 y)) or (x #? (tau 2 y)) or (x #? (tau 3 y)).
Definition bcheck (x y:message):Bool := (isin x ((tau 1 (pi2 (tau 1 y))), ((tau 1 (pi2 (tau 2 y))), (tau 1 (pi2 (tau 3 y)))))).
Definition ncheck (x y:message):Bool := (isin x ((tau 3 (pi2 (tau 1 y))), ((tau 3 (pi2 (tau 2 y))), (tau 3 (pi2 (tau 3 y)))))).
 

Definition lbl:= |(N 100)|.
Definition label x y := If (x #? (tau 2 (pi2 (tau 1 y)))) then (pi1 (tau 1 y))
                           else  (If (x#? (tau 2 (pi2 (tau 2 y)))) then (pi1 (tau 2 y))
                                                       else (If (x #? (tau 2 (pi2 (tau 3 y)))) then (pi1 (tau 3 y))
                                                             else O)).

Definition bnlcheck( x y z:message):Bool:= (bcheck x z) & (|(label x z)| #? lbl) & (ncheck y z).

Definition mvchecks x (n n':nat) := (dist (x n n')) & (pvchecks (x n n')).

Definition p n x := ( (tau 1 (d n x)), (tau 2 (d n x))).
 
Definition sotrm x := (shufl (p 1 x) (p 2 x) (p 3 x)).


Theorem lemma14:  forall (t t0 t1 : message),   let v0 := (V0 (N 0)) in
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
                 let e00 := (enc (c00, ((ub c00 t r0 t2), (N 0))) (pke 11) (er 7)) in
                 let e11 := (enc (c11, ((ub c11 t r1 t3), (N 1))) (pke 11) (er 8)) in
                 let e10 := (enc (c10, ((ub c10 t r0 t4), (N 0))) (pke 11) (er 7)) in
                 let e01 := (enc (c01, ((ub c01 t r1 t5), (N 1))) (pke 11) (er 8)) in
                 let mvtrm0 n n' x := let y := f (toListm ((Phi2 n n') ++ [msg e00, msg e11])) in (If (dist y) & (pvchecks y) then x else |_) in
                 let mvtrm1 n n' x := let y := f (toListm ((Phi2 n n') ++ [msg e10, msg e01])) in (If (dist y) & (pvchecks y) then x else |_) in
                 let f3ph30 n n' x := f (toListm ((Phi2 n n') ++ [msg e00, msg e11, msg (mvtrm0 n n' x)])) in
                 let f3ph31 n n' x := f (toListm ((Phi2 n n') ++ [msg e10, msg e01, msg (mvtrm1 n n' x)])) in
                 let l00 n n' x := (If (bnlcheck c00 (N 0) (f3ph30 n n' x)) then (enc ((label c00 (f3ph30 n n' x)), (k0, THREE))(pke 11) (er 9)) else O) in
                 let l11 n n' x := (If (bnlcheck c11 (N 1) (f3ph30 n n' x)) then (enc ((label c11 (f3ph30 n n' x)), (k1, THREE))(pke 11) (er 10)) else O) in
                 let l10 n n' x := (If (bnlcheck c10 (N 0) (f3ph31 n n' x)) then (enc ((label c10 (f3ph31 n n' x)), (k0, THREE))(pke 11) (er 9)) else O) in
                 let l01 n n' x := (If (bnlcheck c01 (N 1) (f3ph31 n n' x)) then (enc ((label c01 (f3ph31 n n' x)), (k1, THREE))(pke 11) (er 10)) else O) in
                 let f5ph50 n n' x := f (toListm ((Phi2 n n') ++ [msg e00, msg e11, msg (mvtrm0 n n' x), msg (l00 n n' x), msg (l11 n n' x)])) in
                 let f5ph51 n n' x := f (toListm ((Phi2 n n') ++ [msg e10, msg e01, msg (mvtrm1 n n' x), msg (l10 n n' x), msg (l01 n n' x)])) in
                 let motrm0 n n' x := let z := (f5ph50 n n' x) in
                                      let Isin0 := (isin k0 ((tau 2 (d 1 z)), ((tau 2 (d 2 z)), (tau 2 (d 3 z))))) in
                                      let Isin1 := (isin k1 ((tau 2 (d 1 z)), ((tau 2 (d 2 z)), (tau 2 (d 3 z))))) in
                                      (If (dist z) & (pochecks z)& ((Isin0&Isin1) or (! (Isin0 or Isin1))) then (sotrm z) else O) in
                 let motrm1 n n' x := let z := (f5ph51 n n' x) in
                                      let Isin0 := (isin k0 ((tau 2 (d 1 z)), ((tau 2 (d 2 z)), (tau 2 (d 3 z))))) in
                                      let Isin1 := (isin k1 ((tau 2 (d 1 z)), ((tau 2 (d 2 z)), (tau 2 (d 3 z))))) in
                                      (If (dist z) & (pochecks z)& ((Isin0&Isin1) or (! (Isin0 or Isin1))) then (sotrm z) else O) in
                 let pv00 := (c00, ((ub c00 t r0 t2), (N 0))) in
                 let pv10 := (c10, ((ub c10 t r0 t4), (N 0))) in
                 let s0 n n' := let y := f (toListm ((Phi2 n n') ++ [msg e00, msg e11])) in  (If !(isin pv00 ((pi1 (d 1 y)), ((pi1 (d 2 y)), (pi1 (d 3 y))))) then (shufl (pi1 (d 1 y)) (pi1 (d 2 y)) (pi1 (d 3 y))) else O) in
                 let s1 n n' := let y := f (toListm ((Phi2 n n') ++ [msg e10, msg e01])) in  (If !(isin pv10 ((pi1 (d 1 y)), ((pi1 (d 2 y)), (pi1 (d 3 y))))) then (shufl (pi1 (d 1 y)) (pi1 (d 2 y)) (pi1 (d 3 y))) else O) in
                 let lt1 n n' x := (e00, (e11, (mvtrm0 n n' x))) in
                 let lt2 n n' x := ((l00 n n' x), ((l11 n n' x), (motrm0 n n' x))) in
                 let rt1 n n' x := (e10, (e01, (mvtrm1 n n' x))) in
                 let rt2 n n' x := ((l10 n n' x), ((l01 n n' x), (motrm1 n n' x))) in
                 [ msg (bl c00 t r0), msg (bl c11 t r1), msg (If (acc c00 t r0 t2)& (acc c11 t r1 t3) then ((lt1 0 1 (s0 0 1)), (lt2 0 1 (s0 0 1))) else |_)] ~ [msg (bl c10 t r0), msg (bl c01 t r1), msg (If  (acc c10 t r0 t4)& (acc c01 t r1 t5) then ((rt1 1 0 (s1 1 0)), (rt2 1 0 (s1 1 0))) else |_)].

Proof.
intros.
unfold lt1, rt1.
unfold mvtrm0, mvtrm1.
simpl.
unfold lt2, rt2, l00, l11, l10, l01. 
unfold f3ph30.
unfold mvtrm0. unfold motrm0. unfold f5ph50.
unfold l00.
pose proof(ENCCCA2). unfold e00.
pose proof(ENCCCA2 O O (c00, (ub c00 t r0 t2, N 0)) (c00, (ub c00 t r0 t2, N 100)) O 0 11 7 7
                  
                  (   let s0x n n':= (If ! (isin pv00
                                (pi1 (d 1 (f (toListm (Phi2 n n' ++ [msg (Mvar 0), msg e11])))),
                                (pi1 (d 2 (f (toListm (Phi2 n n' ++ [msg (Mvar 0), msg e11])))),
                                pi1 (d 3 (f (toListm (Phi2 n n' ++ [msg (Mvar 0), msg e11])))))))
                           then shufl
                                  (pi1 (d 1 (f (toListm (Phi2 n n' ++ [msg (Mvar 0), msg e11])))))
                                  (pi1 (d 2 (f (toListm (Phi2 n n' ++ [msg (Mvar 0), msg e11])))))
                                  (pi1 (d 3 (f (toListm (Phi2 n n' ++ [msg (Mvar 0), msg e11]))))) 
                else O) in
 let mvtrm0x n n' x := let y := f (toListm ((Phi2 n n') ++ [msg (Mvar 0), msg e11])) in (If (dist y) & (pvchecks y) then x else |_) in
let f3ph30x n n' x := (f
                       (toListm
                          (Phi2 0 1 ++
                           [msg (Mvar 0), msg e11, msg (mvtrm0x n n' x)]))) in

 let l00x n n' x := (If (bnlcheck c00 (N 0) (f3ph30x n n' x)) then (enc ((label c00 (f3ph30x n n' x)), (k0, THREE))(pke 11) (er 9)) else O) in
 let l11x n n' x := (If (bnlcheck c11 (N 1) (f3ph30x n n' x)) then (enc ((label c11 (f3ph30x n n' x)), (k1, THREE))(pke 11) (er 10)) else O) in
 let f5ph50x n n' x := f (toListm ((Phi2 n n') ++ [msg (Mvar 0), msg e11, msg (mvtrm0x n n' x), msg (l00x n n' x), msg (l11x n n' x)])) in
     let motrm0x n n' x := let z := (f5ph50x n n' x) in
                                      let Isin0 := (isin k0 ((tau 2 (d 1 z)), ((tau 2 (d 2 z)), (tau 2 (d 3 z))))) in
                                      let Isin1 := (isin k1 ((tau 2 (d 1 z)), ((tau 2 (d 2 z)), (tau 2 (d 3 z))))) in
                                      (If (dist z) & (pochecks z)& ((Isin0&Isin1) or (! (Isin0 or Isin1))) then (sotrm z) else O) in

     [msg (bl c00 t r0), msg (bl c11 t r1),
   msg
     (If (acc c00 t r0 t2) & (acc c11 t r1 t3)
         then (((Mvar 0),
              (e11, (mvtrm0x 0 1 (s0x 0 1)))),
              (If bnlcheck c00 (N 0) (f3ph30x 0 1 (s0x 0 1))
                  then (enc (label c00 (f3ph30x 0 1 (s0x 0 1)), (k0, THREE)) (pke 11) (er 9)) 
                  else O,
              (If bnlcheck c11 (N 1) (f3ph30x 0 1 (s0x 0 1))
                  then (enc (label c11 (f3ph30x 0 1 (s0x 0 1)), (k1, THREE)) (pke 11) (er 10)) 
                  else O, motrm0x 0 1 (s0x 0 1)))) 
         else |_)])).
simpl in H6.
Definition s0x := (If ! (isin pv00
                                (pi1 (d 1 (f (toListm (Phi2 0 1 ++ [msg (Mvar 0), msg e11])))),
                                (pi1 (d 2 (f (toListm (Phi2 0 1 ++ [msg (Mvar 0), msg e11])))),
                                pi1 (d 3 (f (toListm (Phi2 0 1 ++ [msg (Mvar 0), msg e11])))))))
                           then shufl
                                  (pi1 (d 1 (f (toListm (Phi2 0 1 ++ [msg (Mvar 0), msg e11])))))
                                  (pi1 (d 2 (f (toListm (Phi2 0 1 ++ [msg (Mvar 0), msg e11])))))
                                  (pi1 (d 3 (f (toListm (Phi2 0 1 ++ [msg (Mvar 0), msg e11]))))) 
                           else O).
unfold 
unfold f3ph30.
unfold mvtrm0.
unfold s0.

(** STEP:1 *)
Definition vcheck (v:message) :=  (v #? C1) or (v#?C2) or (v#?C3).
Definition x1:= f (toListm phi0).
Definition pk:= (pubkey x1).
Axiom vote_len_reg : forall t, (|V0 t| #? |V1 t|) ## TRue.
(** * Phase 1:Authentication *)
(** nA = 0, nB = 1, nM = 2 *)
Eval compute in ssk.
Definition v (n:nat) := match n with
                        | 0 => V0 (x1)
                        | 1 => V1 (x1)
                        | _ => O
                        end.

Eval compute in kc.

Definition ssk (n:nat) := pi2 (ks (N n)).
Definition k0 := (kc (N 3)) .
Definition k1 := (kc (N 4)).
Definition rb0 := (rb (N 5)).
Definition rb1 := (rb (N 6)).
Definition ssk0 := (ssk 0).
Definition ssk1 := (ssk 1).
Definition rs0 := (rs (N 9)).
Definition rs1 := (rs (N 10)).

Definition c (n k: nat) := (comm (v n) (kc (N k))).
Definition b (n k r : nat) := (bl (c n k) pk (rb (N r))).
Definition s (n k r n' r' : nat) := (sign (b n k r) (ssk n') (rs (N r'))).
Definition tr (a n k r r':nat) := ( (vk a), ((b n k r), (s n k r a r'))).
 
Definition theta (x a: message) :=  ((to x) #? a) & (vcheck (v 0))&(vcheck (v  1)).

Definition t1 (n n':nat)  := If (theta x1 A) then (tr 0 n 3 5 9) else (If (theta x1 B) then (tr 1 n' 4 6 10) else O). 

Definition phi1 (n n':nat) := phi0 ++ [msg (t1 n n')]. 



(** Indistinguishability proof of frame phi1 *)



(** Actually, we dont need this lengthy proof as we can always prove the indistinguishability of longer frames and use [RESTR] to get the indistinguishability of the smaller ones *)
(*
Theorem frame1_ind : (phi1 0 1) ~ (phi1 1 0).
Proof. intros.
unfold phi1.
simpl. unfold t1. simpl.
 simpl. apply IFBRANCH_M1 with (ml1:= phi0) (ml2:= phi0).
simpl. repeat unfold theta, tr, s, b, c.
simpl.

pose proof (let x1:= f (toListm phi0) in
            let v0 := V0(x1) in
            let v1 := V1(x1) in
            let k0 := (kc (N 3)) in
            let k1 := (kc (N 4)) in
            let rb0 := (rb (N 5)) in
            let rb1 := (rb (N 6)) in
            let rs0 := (rs (N 7)) in
            let rs1 := (rs (N 8)) in
            let ssk0 := pi2 (ks (N 9)) in
            let ssk1 := pi2 (ks (N 10)) in
            compHid 3 4 O (V0(f (toListm phi0)))  (V1(f (toListm phi0))) (phi0++[msg x1, bol ((to x1) #? A) & (vcheck v0)&(vcheck v1),  msg rb0, msg rb1, msg rs0, msg rs1, msg ssk0, msg ssk1])).
simpl in H.
assert ( (| V0 x1 | #? |V1 x1|) ## TRue).
apply vote_len_reg. simpl in H0.
repeat rewrite H0 in H. repeat rewrite IFTRUE_M in H. 
funappf1 pi1 21 H.
funappf1 pi2 22 H.
repeat rewrite proj1, proj2 in H.
funappf1 pubkey 15 H. 
fold x1. 
funapptrmhyp (msg (bl (comm (V0 x1) (kc (N 3))) (pubkey x1) (rb (N 5)))) (msg (bl (comm (V1 x1) (kc (N 3))) (pubkey x1) (rb (N 5)))) H;simpl; try reflexivity. 
 
funapptrmhyp (msg (sign (bl (comm (V0 x1) (kc (N 3))) (pubkey x1) (rb (N 5))) 
       (pi2 (ks (N 9))) (rs (N 7)))) (msg (sign (bl (comm (V1 x1) (kc (N 3))) (pubkey x1) (rb (N 5))) (pi2 (ks (N 9))) (rs (N 7)))) H;simpl; try reflexivity.
funapptrmhyp (msg (bl (comm (V0 x1) (kc (N 3))) (pubkey x1) (rb (N 5)),
     sign (bl (comm (V0 x1) (kc (N 3))) (pubkey x1) (rb (N 5))) 
       (pi2 (ks (N 9))) (rs (N 7)))) (msg (bl (comm (V1 x1) (kc (N 3))) (pubkey x1) (rb (N 5)),
    sign (bl (comm (V1 x1) (kc (N 3))) (pubkey x1) (rb (N 5))) 
      (pi2 (ks (N 9))) (rs (N 7)))) H; simpl; try reflexivity.
funapptrmhyp (msg (vk 0,
     (bl (comm (V0 x1) (kc (N 3))) (pubkey x1) (rb (N 5)),
     sign (bl (comm (V0 x1) (kc (N 3))) (pubkey x1) (rb (N 5))) 
       (pi2 (ks (N 9))) (rs (N 7))))) (msg (vk 0,
    (bl (comm (V1 x1) (kc (N 3))) (pubkey x1) (rb (N 5)),
    sign (bl (comm (V1 x1) (kc (N 3))) (pubkey x1) (rb (N 5))) 
      (pi2 (ks (N 9))) (rs (N 7))))) H; simpl; try reflexivity.

restrsublis H.  auto. simpl; try reflexivity.  simpl. reflexivity. try split.
reflexivity. split. reflexivity. reflexivity.
(** branch 2 *)

simpl.
repeat unfold theta, tr, s, b, c.
apply IFBRANCH_M1 with (ml1:= [msg A, msg B, msg M, msg C1, msg C2, msg C3, msg ONE, 
   msg TWO, msg THREE, msg (vk 0), msg (vk 1), msg (pke 2),
   bol ((to x1) #? A) & (vcheck (v 0)) & (vcheck (v 1))]) (ml2:= [msg A, msg B, msg M, msg C1, msg C2, msg C3, msg ONE, 
   msg TWO, msg THREE, msg (vk 0), msg (vk 1), msg (pke 2),
   bol ((to x1) #? A) & (vcheck (v 0)) & (vcheck (v 1))]). simpl.

pose proof (let x1:= f (toListm phi0) in
            let v0 := V0(x1) in
            let v1 := V1(x1) in
            let k0 := (kc (N 3)) in
            let k1 := (kc (N 4)) in
            let rb0 := (rb (N 5)) in
            let rb1 := (rb (N 6)) in
            let rs0 := (rs (N 7)) in
            let rs1 := (rs (N 8)) in
            let ssk0 := pi2 (ks (N 9)) in
            let ssk1 := pi2 (ks (N 10)) in
            compHid 3 4 O (V0(f (toListm phi0)))  (V1(f (toListm phi0))) (phi0++[msg x1,bol ((to x1) #? A) & (vcheck (V1 x1)) & (vcheck (V0 x1)),
   bol ((to x1) #? B) & (vcheck (V1 x1)) & (vcheck (V0 x1)),msg rb0, msg rb1, msg rs0, msg rs1, msg ssk0, msg ssk1])).
simpl in H.
assert ( let x1:= f (toListm phi0) in (| V0 x1 | #? |V1 x1|) ## TRue).
apply vote_len_reg. repeat rewrite H0 in H. repeat rewrite IFTRUE_M in H.
 
 funappf1 pi1 22 H.
funappf1 pi2 23 H.
repeat rewrite proj1, proj2 in H. 
 funapptrmhyp (msg (bl (comm (V1 x1) (kc (N 4))) (pubkey x1) (rb (N 6)))) (msg (bl (comm (V0 x1) (kc (N 4))) (pubkey x1) (rb (N 6)))) H;simpl; try reflexivity.
   
funapptrmhyp (msg (sign (bl (comm (V1 x1) (kc (N 4))) (pubkey x1) (rb (N 6))) 
       (pi2 (ks (N 10))) (rs (N 8)))) (msg (sign (bl (comm (V0 x1) (kc (N 4))) (pubkey x1) (rb (N 6))) (pi2 (ks (N 10))) (rs (N 8)))) H;simpl; try reflexivity. 
funapptrmhyp (msg (bl (comm (V1 x1) (kc (N 4))) (pubkey x1) (rb (N 6)),
     sign (bl (comm (V1 x1) (kc (N 4))) (pubkey x1) (rb (N 6))) 
       (pi2 (ks (N 10))) (rs (N 8)))) (msg (bl (comm (V0 x1) (kc (N 4))) (pubkey x1) (rb (N 6)),
    sign (bl (comm (V0 x1) (kc (N 4))) (pubkey x1) (rb (N 6))) 
      (pi2 (ks (N 10))) (rs (N 8)))) H; simpl; try reflexivity.
funapptrmhyp (msg (vk 1,
     (bl (comm (V1 x1) (kc (N 4))) (pubkey x1) (rb (N 6)),
     sign (bl (comm (V1 x1) (kc (N 4))) (pubkey x1) (rb (N 6))) 
       (pi2 (ks (N 10))) (rs (N 8))))) (msg (vk 1,
    (bl (comm (V0 x1) (kc (N 4))) (pubkey x1) (rb (N 6)),
    sign (bl (comm (V0 x1) (kc (N 4))) (pubkey x1) (rb (N 6))) 
      (pi2 (ks (N 10))) (rs (N 8))))) H; simpl; try reflexivity.

 restrsublis H; try assumption;  simpl; try reflexivity. repeat (simpl; try split; try reflexivity).  reflexivity.
Qed.

*)

(** STEP: 2 *)


Definition x2t (n:nat) := f (toListm (phi0 ++ [msg (tr 0 n 3  5 9)])).

Eval compute in x2t 0.
Definition x2ft (n':nat) := f (toListm (phi0 ++ [msg (tr 1 n' 4 6 10)])).

Definition t2 (n n': nat) := If (theta x1 A) then (If (theta (x2t n) B) then (tr 1 n' 4 6 10) else O) else (If (theta x1 B) then (If (theta (x2ft n') A) then (tr 0 n 3 5 9) else O) else O). 
 
Definition phi2 (n n':nat) := (phi1 n n') ++ [msg (t2 n n') ].
Print IFEVAL_B'.
Axiom ext_ifeval: forall b1 b2 b3 x y, (IF b1 & (!b2)&(!b3) then x else y) ## (IF b1 & (!b2)&(!b3) then (subbol_bol' b1 TRue (subbol_bol' b2 FAlse (subbol_bol' b3 FAlse x))) else  (subbol_bol' b1 FAlse (subbol_bol' b2 TRue (subbol_bol' b3 TRue y)))).
Axiom eqbrmsg_msg'' :forall ( m m1 m2:message) (b1 b2: Bool) ,  (IF (m1 #? m2) then (submsg_bol' m m1 b1) else b2) ##  (IF (eqm m1 m2) then (submsg_bol' m m2 b1) else b2).

Ltac aply_eqbr :=
match goal with
| [|-  context [IF (?X #? ?Y) then ?B1 else ?B2] ] => pose proof (eqbrmsg_msg'' X X Y B1 B2)
end.
(** Using ext_comp_hid **)
Eval compute in (v 0).
Theorem vote_len_eql: (IF (vcheck (v 0)) & (vcheck (v 1)) then |(v 0)|#? |(v 1)| else TRue) ## TRue.
Proof. unfold vcheck.


       rewrite <- IFSAME_B with (b:= ((v 0) #? C1)).
rewrite IFEVAL_B'.
simpl.
repeat redg.
aply_eqbr.
simpl in H.
rewrite H.
clear H.
rewrite <- IFSAME_B with (b:= ((v 1) #? C1)).
rewrite IFEVAL_B'.
simpl.
repeat redg.
aply_eqbr.
simpl in H.
repeat red_in H.
rewrite eqmeql in H. repeat red_in H.
rewrite H; clear H.
rewrite <- IFSAME_B with (b:= ((v 0) #? C2)).
rewrite IFEVAL_B' ; repeat redg.
simpl.
repeat redg.
aply_eqbr.
simpl in H.
pose proof(candEql1).
Axiom Example14_M': forall m1 m2, (m1 #? m2) ## (m2 #? m1).

rewrite Example14_M' in H0.
rewrite H0 in H.
repeat red_in H. rewrite H.
rewrite <- IFSAME_B with (b:= ((v 1) #? C2)).
rewrite IFEVAL_B'.
simpl.
repeat redg.
aply_eqbr.
simpl in H1.
repeat rewrite eqmeql in H1.
repeat red_in H1.
rewrite Example14_M' in H0.
rewrite H0 in H1; repeat red_in H1.
rewrite H1. clear H1. clear H.
rewrite <- IFSAME_B with (b:= ((v 0) #? C3)).
rewrite IFEVAL_B'.
simpl.
repeat redg.
aply_eqbr.
simpl in H.
repeat red_in H.
pose proof (candEql2).
pose proof (candEql3).
rewrite Example14_M' in H1.

repeat rewrite H1 in H.
rewrite Example14_M' in H2.
rewrite H2 in H. repeat red_in H.
rewrite H.
clear H.
rewrite <- IFSAME_B with (b:= ((v 1) #? C3)).
rewrite IFEVAL_B'.
simpl.
repeat redg.
aply_eqbr.
simpl in H.
rewrite Example14_M' in H2.
repeat rewrite H2 in H.
rewrite Example14_M' in H0.
repeat rewrite H0 in H.
rewrite Example14_M' in H1.
repeat rewrite H1 in H.
repeat rewrite eqmeql in H.
repeat red_in H. rewrite H.
reflexivity.
Qed.
(** Go back apply ext_comphid in this way in prop1 and voting_prop*)
Axiom compHid_ext': forall (n2 n3 n4 n5:nat) (t2 t3 : message) {n} {m} (z: mylist n) (l:mylist m), closMylist [msg t2, msg t3] = true /\ closMylist z = true /\ Fresh [n2; n3] (z++[msg t2, msg t3]) = true  ->
                                                                                ((length (distMvars l))=? 2)%nat = true -> 
                                                                                let mvl:= [n4; n5] in ((distMvars l) = mvl \/ (distMvars l) = [n5; n4])  ->
                                                                                                        
                                                                                                         let m0 := (comm t2 (k n2)) in
                                                                                                         let m1 := (comm t3 (k n3)) in
                                                                                                         let m0':= (comm t3 (k n2)) in
                                                                                                         let m1':= (comm t2 (k n3)) in 
                                                                                                                                                          
(z ++ ([n4 <- (If |t2|#?|t3| then m0 else O)]([n5 <- (If |t2|#?|t3| then m1 else O)]l))) ~ (z ++ ([n4 <- (If |t2|#?|t3| then m0' else O)]([n5 <- (If |t2|#?|t3| then m1' else O)]l))).


Axiom ifmr_gen1_msg: forall f b t1 t2, (f (If b then t1 else t2)) # (If b then (f t1) else (f t2)).
Axiom ifmr_gen21_msg: forall (f:message->message->message) t b t1 t2, (f (If b then t1 else t2) t) # (If b then (f t1 t) else (f t2 t)).
Axiom ifmr_gen22_msg: forall (f:message->message->message) t b t1 t2, (f t (If b then t1 else t2)) # (If b then (f t t1) else (f t t2)).
Axiom ifmr_gen31_msg: forall (f:message->message->message->message) s t b t1 t2, (f (If b then t1 else t2) s t) # (If b then (f t1 s t) else (f t2 s t)).
Axiom ifmr_gen32_msg: forall (f:message->message->message->message) s t b t1 t2, (f s  (If b then t1 else t2) t) # (If b then (f s t1 t) else (f s t2 t)).
Axiom ifmr_gen33_msg: forall (f:message->message->message->message) s t b t1 t2, (f s t (If b then t1 else t2)) # (If b then (f s t t1) else (f s t t2)).
Axiom ifmr_gen33b_msg: forall (f:Bool->message->message->message) s t b t1 t2, (f s t (If b then t1 else t2)) # (If b then (f s t t1) else (f s t t2)).
Axiom ifmr_gen31b_msg: forall (f:Bool->message->message->message) s t b t1 t2, (f (IF b then t1 else t2) s t) # (If b then (f t1 s t) else (f t2 s t)).
Axiom ifmr_gen32b_msg: forall (f:Bool->message->message->message) s t b t1 t2, (f s  (If b then t1 else t2) t) # (If b then (f s t1 t) else (f s t2 t)).

Axiom ifmr_gen1_bol: forall f b t1 t2, (f (IF b then t1 else t2)) ## (IF b then (f t1) else (f t2)).
Axiom ifmr_gen21_bol: forall (f:Bool-> Bool->Bool) t b t1 t2, (f t (IF b then t1 else t2)) ## (IF b then (f t t1) else (f t t2)).
Axiom ifmr_gen22_bol: forall (f:Bool->Bool->Bool) t b t1 t2, (f (IF b then t1 else t2) t) ## (IF b then (f t1 t) else (f t2 t)).
Axiom ifmr_gen21m_bol: forall (f:message->message->Bool) t b t1 t2, (f t (If b then t1 else t2)) ## (IF b then (f t t1) else (f t t2)).
Axiom ifmr_gen22m_bol: forall (f:message->message->Bool) t b t1 t2, (f (If b then t1 else t2) t) ## (IF b then (f t1 t) else (f t2 t)).


Axiom ifmr_gen31_bol: forall (f:Bool->Bool->Bool->Bool) s t b t1 t2, (f (IF b then t1 else t2) s t) ## (IF b then (f t1 s t) else (f t2 s t)).
Axiom ifmr_gen32_bol: forall (f:Bool->Bool->Bool->Bool) s t b t1 t2, (f s  (IF b then t1 else t2) t) ## (IF b then (f s t1 t) else (f s t2 t)).
Axiom ifmr_gen33_bol: forall (f:Bool->Bool->Bool->Bool) s t b t1 t2, (f s t (IF b then t1 else t2)) ## (IF b then (f s t t1) else (f s t t2)).

  Theorem frame2_ind: (|v 0| #? |v 1|) ## TRue -> (phi2 0 1) ~ (phi2 1 0). 
Proof. intros. unfold phi2, phi1. unfold t1, t2. simpl.
       unfold x2t, x2ft, tr, theta. repeat unfold b, s.
       unfold andB.
       pose proof(compHid_ext). 
pose proof(compHid_ext 3 4 0 1 (v 0) (v 1) [] (phi0++
[msg
     (If IF (to x1) #? A then IF vcheck (v 0) then vcheck (v 1) else FAlse else FAlse
         then (vk 0, (bl (Mvar 0) pk (rb (N 5)), sign (bl (Mvar 0) pk (rb (N 5))) (ssk 0) (rs (N 9)))) 
         else If IF (to x1) #? B then IF vcheck (v 0) then vcheck (v 1) else FAlse else FAlse
                 then (vk 1, (bl (Mvar 1) pk (rb (N 6)), sign (bl (Mvar 1) pk (rb (N 6))) (ssk 1) (rs (N 10)))) 
                 else O),
   msg
     (If IF (to x1) #? A then IF vcheck (v 0) then vcheck (v 1) else FAlse else FAlse
         then If IF (to
                       (f
                          (toListm
                             (phi0 ++
                              [msg (vk 0, (bl (Mvar 0) pk (rb (N 5)), sign (bl (Mvar 0) pk (rb (N 5))) (ssk 0) (rs (N 9))))])))) #?
                    B then IF vcheck (v 0) then vcheck (v 1) else FAlse else FAlse
                 then (vk 1, (bl (Mvar 1) pk (rb (N 6)), sign (bl (Mvar 1) pk (rb (N 6))) (ssk 1) (rs (N 10)))) 
                 else O 
         else If IF (to x1) #? B then IF vcheck (v 0) then vcheck (v 1) else FAlse else FAlse
                 then If IF (to
                               (f
                                  (toListm
                                     (phi0 ++
                                      [msg
                                         (vk 1, (bl (Mvar 1) pk (rb (N 6)), sign (bl (Mvar 1) pk (rb (N 6))) (ssk 1) (rs (N 10))))]))))
                            #? A then IF vcheck (v 0) then vcheck (v 1) else FAlse else FAlse
                         then (vk 0, (bl (Mvar 0) pk (rb (N 5)), sign (bl (Mvar 0) pk (rb (N 5))) (ssk 0) (rs (N 9)))) 
                         else O 
                 else O)])).
simpl in H1.
apply H1.
repeat (try split; auto).
reflexivity. unfold distMvars.
simpl; right. trivial. 

Qed.
(** Using FUNCApp and Comphid **)
(*
Theorem frame2_ind: (phi2 0 1) ~ (phi2 1 0).
Proof. repeat unfold phi2, phi1, theta, tr, s, b, c, t1, t2. simpl. 
apply IFBRANCH_M2 with (ml1:= phi0) (ml2:=phi0). simpl.
 
apply IFBRANCH_M1 with (ml1:= phi0 ++ [bol (theta x1 A), msg (tr 0 0 3 5 9)]) (ml2:= phi0 ++ [bol (theta x1 A), msg (tr 0 1 3 5 9)]).
repeat unfold phi2, phi1, theta, tr, s, b, c, t1, t2. simpl. 
pose proof (compHid 3 4 O (V0 x1) (V1 x1) (phi0++[msg x1,  bol (vcheck (v 0)), bol (vcheck (v 1)), bol ((to x1) #? A) & (vcheck (v 0))&(vcheck (v 1)),  msg rb0, msg rb1, msg rs0, msg rs1, msg ssk0, msg ssk1, bol FAlse, bol TRue])).
simpl in H.
assert ( (| V0 x1 | #? |V1 x1|) ## TRue).
apply vote_len_reg. simpl in H0.
repeat rewrite H0 in H. repeat rewrite IFTRUE_M in H.  
funappf1 pi1 25 H.
funappf1 pi2 26 H.
repeat rewrite proj1, proj2 in H.
funappf1 pubkey 15 H.
clear H0.
(** construct bool condition *)  
 unfold rb0, rb1, rs0, rs1, ssk0, ssk1 in H.
 funapptrmhyp (msg (b 0 3 5)) (msg (b 1 3 5)) H; simpl; try reflexivity.
 
funapptrmhyp (msg (s 0 3 5 0 9)) (msg (s 1 3 5 0 9)) H; simpl; try reflexivity.
funapptrmhyp (msg (tr 0 0 3 5 9)) (msg (tr 0 1 3 5 9)) H; simpl; try reflexivity.
funapptrmhyp (msg (x2t 0)) (msg (x2t 1)) H; simpl; try reflexivity.
funapptrmhyp (msg (to (x2t 0))) (msg (to (x2t 1))) H; simpl; try reflexivity.
funapptrmhyp  (bol ((to (x2t 0)) #? B) & (vcheck (V0 x1)) & (vcheck (V1 x1))) ( bol ((to (x2t 1)) #? B) & (vcheck (V0 x1)) & (vcheck (V1 x1))) H; simpl; try reflexivity. 
funapptrmhyp (msg (bl (comm (V1 x1) (kc (N 4))) pk (rb (N 6)))) (msg (bl (comm (V0 x1) (kc (N 4))) pk (rb (N 6)))) H; simpl; try reflexivity.  
funapptrmhyp (msg (s 1 4 6 1 10)) (msg (s 0 4 6 1 10)) H; simpl; try reflexivity.

funapptrmhyp (msg (tr 1 1 4 6 10)) (msg (tr 1 0 4 6 10)) H; simpl; try reflexivity.

(** reduce the goal *)
restrsublis H. auto.
repeat (simpl; try reflexivity).
simpl.
reflexivity.
repeat ( simpl; try split; try reflexivity).


(** goal-2 *)

pose proof (compHid 3 4 O (V0 x1) (V1 x1) (phi0++[msg x1,  bol (vcheck (v 0)), bol (vcheck (v 1)), bol ((to x1) #? A) & (vcheck (v 0))&(vcheck (v 1)),  msg rb0, msg rb1, msg rs0, msg rs1, msg ssk0, msg ssk1, bol FAlse, bol TRue])).
simpl in H.
assert ( (| V0 x1 | #? |V1 x1|) ## TRue).
apply vote_len_reg. simpl in H0.
repeat rewrite H0 in H. repeat rewrite IFTRUE_M in H.  
funappf1 pi1 25 H.
funappf1 pi2 26 H.
repeat rewrite proj1, proj2 in H.
funappf1 pubkey 15 H.
clear H0.

(** construct bool condition *)
funapptrmhyp (msg (b 0 3 5)) (msg (b 1 3 5)) H; simpl; try reflexivity.
funapptrmhyp (msg (s 0 3 5 0 9)) (msg (s 1 3 5 0 9)) H; simpl; try reflexivity.
funapptrmhyp (msg (tr 0 0 3 5 9)) (msg (tr 0 1 3 5 9)) H; simpl; try reflexivity.
funapptrmhyp (msg (x2t 0)) (msg (x2t 1)) H; simpl; try reflexivity.
funapptrmhyp (msg (to (x2t 0))) (msg (to (x2t 1))) H; simpl; try reflexivity.
funapptrmhyp  (bol ((to (x2t 0)) #? B) & (vcheck (V0 x1)) & (vcheck (V1 x1))) ( bol ((to (x2t 1)) #? B) & (vcheck (V0 x1)) & (vcheck (V1 x1))) H; simpl; try reflexivity.  repeat unfold rb0, rb1, rs0, rs1, ssk0, ssk1 in H.
repeat unfold tr.
(** reduce the goal *)
restrsublis H. auto.
repeat (simpl; try reflexivity).
simpl.
reflexivity.
repeat ( simpl; try split; try reflexivity).
simpl.

(** goal 3 *)

apply IFBRANCH_M2 with (ml1:= phi0 ++[ bol ((to x1) #? A) & (vcheck (V0 x1)) & (vcheck (V1 x1))] )  (ml2:=phi0 ++ [ bol ((to x1) #? A) & (vcheck (V0 x1)) & (vcheck (V1 x1))]). simpl.
 
apply IFBRANCH_M1 with (ml1:= phi0 ++ [bol (theta x1 A), bol (theta x1 B), msg (tr 1 1 4 6 10)]) (ml2:= phi0 ++ [bol (theta x1 A), bol (theta x1 B), msg (tr 1 0 4 6 10)]).

repeat unfold phi2, phi1, theta, tr, s, b, c, t1, t2. simpl. 
pose proof (compHid 4 3 O (V1 x1) (V0 x1) (phi0++[msg x1,  bol (vcheck (v 0)), bol (vcheck (v 1)),  bol ((to x1) #? A), bol ((to x1) #? B), msg rb0, msg rb1, msg rs0, msg rs1, msg ssk0, msg ssk1, bol FAlse, bol TRue])).
simpl in H.
Axiom eqm_refl: forall m1 m2, (m1 #? m2) ## TRue -> (m2 #? m1) ## TRue.
assert ( (| V0 x1 | #? |V1 x1|) ## TRue).
apply vote_len_reg. simpl in H.
apply eqm_refl in H0.
repeat rewrite H0 in H. repeat rewrite IFTRUE_M in H.  
funappf1 pi1 26 H.
funappf1 pi2 27 H.
repeat rewrite proj1, proj2 in H.
funappf1 pubkey 15 H.
clear H0.
(** construct bool condition *)
Eval compute in (x2ft 1).
funapptrmhyp (msg (b 1 4 6)) (msg (b 0 4 6)) H; simpl; try reflexivity.
funapptrmhyp (msg (s 1 4 6 1 10)) (msg (s 0 4 6 1 10)) H; simpl; try reflexivity.
funapptrmhyp (msg (tr 1 1 4 6 10)) (msg (tr 1 0 4 6 10)) H; simpl; try reflexivity.


funapptrmhyp (msg (x2ft 1)) (msg (x2ft 0)) H; simpl; try reflexivity.
funapptrmhyp (msg (to (x2ft 1))) (msg (to (x2ft 0))) H; simpl; try reflexivity.
 funapptrmhyp (bol ((to (x2ft 1)) #? B)) (bol ((to (x2ft 0)) #? B)) H; simpl; try reflexivity.
funapptrmhyp (bol (vcheck (V0 x1))& (vcheck (V1 x1))) (bol (vcheck (V0 x1))& (vcheck (V1 x1))) H; simpl; try reflexivity. 
 funapptrmhyp  (bol ((to (x2ft 1)) #? B) & (vcheck (V0 x1)) & (vcheck (V1 x1))) ( bol ((to (x2ft 0)) #? B) & (vcheck (V0 x1)) & (vcheck (V1 x1))) H; simpl; try reflexivity.

funapptrmhyp (bol ((to x1) #? B) & (vcheck (V0 x1)) & (vcheck (V1 x1))) (bol ((to x1) #? B) & (vcheck (V0 x1)) & (vcheck (V1 x1))) H; simpl; try reflexivity.
 

funapptrmhyp (msg (b 0 3 5)) (msg (b 1 3 5)) H; simpl; try reflexivity.
funapptrmhyp (msg (s 0 3 5 0 9)) (msg (s 1 3 5 0 9)) H; simpl; try reflexivity.
funapptrmhyp (msg (tr 0 0 3 5 9)) (msg (tr 0 1 3 5 9)) H; simpl; try reflexivity.


(** reduce the goal *)
restrsublis H. auto.
repeat (simpl; try reflexivity).
simpl.
reflexivity.
repeat ( simpl; try split; try reflexivity).
simpl.

(** goal-2 *)

pose proof (compHid 4 3 O (V1 x1) (V0 x1) (phi0++[msg x1,  bol (vcheck (v 0)), bol (vcheck (v 1)),  bol ((to x1) #? A), bol ((to x1) #? B), msg rb0, msg rb1, msg rs0, msg rs1, msg ssk0, msg ssk1, bol FAlse, bol TRue])).
simpl in H.

assert ( (| V0 x1 | #? |V1 x1|) ## TRue).
apply vote_len_reg. simpl in H0. apply eqm_refl in H0.
repeat rewrite H0 in H. repeat rewrite IFTRUE_M in H.  
funappf1 pi1 26 H.
funappf1 pi2 27 H.
repeat rewrite proj1, proj2 in H.
funappf1 pubkey 15 H.
clear H0.

(** construct bool condition *)
funapptrmhyp (msg (b 1 4 6)) (msg (b 0 4 6)) H; simpl; try reflexivity.
funapptrmhyp (msg (s 1 4 6 1 10)) (msg (s 0 4 6 1 10)) H; simpl; try reflexivity.
funapptrmhyp (msg (tr 1 1 4 6 10)) (msg (tr 1 0 4 6 10))  H; simpl; try reflexivity.
funapptrmhyp (msg (x2ft 1)) (msg (x2ft 0)) H; simpl; try reflexivity.
funapptrmhyp (msg (to (x2ft 1))) (msg (to (x2ft 0))) H; simpl; try reflexivity.
funapptrmhyp  (bol ((to (x2ft 1)) #? A) & (vcheck (V0 x1)) & (vcheck (V1 x1))) ( bol ((to (x2ft 0)) #? A) & (vcheck (V0 x1)) & (vcheck (V1 x1))) H; simpl; try reflexivity.  repeat unfold rb0, rb1, rs0, rs1, ssk0, ssk1 in H.
repeat unfold tr.


(** reduce the goal *)
restrsublis H. auto.
repeat (simpl; try reflexivity).
simpl.
reflexivity.
repeat ( simpl; try split; try reflexivity).
simpl. reflexivity.
Qed. *)

Theorem frame1ind: (| V0 x1 |) #? (| V1 x1 |) ## TRue -> (phi1 0 1) ~ (phi1 1 0).
Proof. intros. unfold phi1.
simpl. pose proof (frame2_ind).
unfold phi2, phi1 in H.  
simpl in H.
apply H0 in H.
dropLast_in H; auto.
Qed.

