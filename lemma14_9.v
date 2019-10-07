 
(************************************************************************)
(* Copyright (c) 2017-2018, Ajay Kumar Eeralla <ae266@mail.missouri.edu>*)     
(************************************************************************)
     
Require Export lemma14_8. 

Set Nested Proofs Allowed.
Section lemma14_9.

  Axiom ext_blind_enc:  forall {n} (t t0 t1 : message) (z:mylist n), let v0 := (V0 (N 0)) in

                                                                     let v1 := (V1 (N 0)) in
                                                                                                      (|v0|#?|v1|) ## TRue ->  (Fresh [1; 2; 3; 4] ([msg t, msg v0, msg v1, msg t0, msg t1])  = true) ->  closMylist ([msg t]) = true -> ((Datatypes.length (distMvars [msg t0, msg t1]))=?  2)%nat = true -> bVarMylist [msg t0, msg t1] = nil  ->
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
                 let e00 := (enc ((c00, ((ub c00 t r0 t2), (N 0))), TWO) (pke 11) (er 7)) in
                 let e11 := (enc ((c11, ((ub c11 t r1 t3), (N 1))), TWO) (pke 11) (er 8)) in
                 let e10 := (enc ((c10, ((ub c10 t r0 t4), (N 0))), TWO) (pke 11) (er 7)) in
                 let e01 := (enc ((c01, ((ub c01 t r1 t5), (N 1))), TWO) (pke 11) (er 8)) in
                 (occur_name_mylist 100 [msg t, msg t0, msg t1] = false) ->
                 (z++[msg (bl c00 t r0), msg (bl c11 t r1), bol (acc c00 t r0 t2)& (acc c11 t r1 t3),
                        msg (If (acc c00 t r0 t2)& (acc c11 t r1 t3) then (((e00, e11), ((c00, k0), (c11, k1))), ((c00, ((ub c00 t r0 t2), (N 0))), (c11, ((ub c11 t r1 t3), (N 1))))) else |_ )])
                    ~
                   
                    (z++[msg (bl c10 t r0), msg (bl c01 t r1), bol (acc c10 t r0 t4)& (acc c01 t r1 t5), 
                           msg (If (acc c10 t r0 t4)& (acc c01 t r1 t5) then (((e10, e01),((c01, k1), (c10, k0))), ((c01, ((ub c01 t r1 t5), (N 1))),(c10, ((ub c10 t r0 t4), (N 0))))) else |_)]).
 (** This is the lemma14. *) 
Lemma rep_none: forall t t0 t1 : message,
      let v0 := V0 (N 0) in
      let v1 := V1 (N 0) in
      (| v0 |) #? (| v1 |) ## TRue ->
      Fresh [1; 2; 3; 4] [msg t, msg v0, msg v1, msg t0, msg t1] = true ->
      closMylist [msg t] = true ->
      (Datatypes.length (distMvars [msg t0, msg t1]) =? 2)%nat = true ->
      bVarMylist [msg t0, msg t1] = nil ->
      let mvl := [5; 6] in
      mVarMsg t0 = mvl /\ mVarMsg t1 = mvl ->
                
                 let r0 := (r 1) in
                 let r1 := (r 2) in
                 let k0 := (kc (N 3)) in
                 let k1 := (kc (N 4)) in
                 let c00 := (comm v0 k0) in
                 let c01 := (comm v0 k1) in
                 let c10 := (comm v1 k0) in
                 let c11 := (comm v1 k1) in
                 let b00 := (bl c00 t r0) in
                 let b11 := (bl c11 t r1) in
                 let b10 := (bl c10 t r0) in
                 let b01 := (bl c01 t r1) in
                 let t2 := ({{ 5 := (bl c00 t r0) }} ({{ 6:=(bl c11 t r1) }} t0)) in
                 let t3 := ({{ 5 := (bl c00 t r0) }} ({{ 6:=(bl c11 t r1) }} t1)) in
                 let t4 := ({{ 5 := (bl c10 t r0) }} ({{ 6:=(bl c01 t r1) }} t0)) in
                 let t5 := ({{ 5 := (bl c10 t r0) }} ({{ 6:=(bl c01 t r1) }} t1)) in
                 let e00 := (enc ((c00, ((ub c00 t r0 t2), (N 0))), TWO) (pke 11) (er 7)) in
                 let e11 := (enc ((c11, ((ub c11 t r1 t3), (N 1))), TWO) (pke 11) (er 8)) in
                 let e10 := (enc ((c10, ((ub c10 t r0 t4), (N 0))), TWO) (pke 11) (er 7)) in
                 let e01 := (enc ((c01, ((ub c01 t r1 t5), (N 1))), TWO) (pke 11) (er 8)) in
                 let pv00 := (c00, ((ub c00 t r0 t2), (N 0))) in
                 let pv11 := (c11, ((ub c11 t r1 t3), (N 1))) in
                 let pv10 := (c10, ((ub c10 t r0 t4), (N 0))) in
                 let pv01 := (c01, ((ub c01 t r1 t5), (N 1))) in
                 let phi02:= [msg b00, msg b11, msg e00, msg e11] in
                 let phi12:= [msg b10, msg b01, msg e10, msg e01] in
                 let fphi02:= f (toListm phi02) in 
                 let s0 := (If (e00 #? (tau 1 fphi02)) & (e11 #? (tau 2 fphi02)) then (shufl pv00 pv11 (pi1 (d 3 fphi02)))
                            else (If (e00 #? (tau 1 fphi02)) & (e11 #? (tau 3 fphi02)) then (shufl pv00 (pi1 (d 2 fphi02)) pv11)
                                  else (If (e00 #? (tau 2 fphi02)) & (e11 #? (tau 1 fphi02)) then (shufl pv11 pv00  (pi1 (d 3 fphi02)))
                                        else (If (e00 #? (tau 3 fphi02)) & (e11 #? (tau 1 fphi02)) then (shufl pv11  (pi1 (d 2 fphi02)) pv00)
                                              else (If (e00 #? (tau 2 fphi02)) & (e11 #? (tau 3 fphi02)) then (shufl  (pi1 (d 1 fphi02)) pv11 pv00)
                                                    else (If (e00 #? (tau 3 fphi02)) & (e11 #? (tau 2 fphi02)) then (shufl  (pi1 (d 1 fphi02)) pv00 pv11)
                                                          else O)))))) in
                
                                
                 let dv0 := (If (dist fphi02) & (pvchecks fphi02) then s0 else |_) in
                 let fphi12:= f (toListm phi12) in 
                  let s1 := (If (e10 #? (tau 1 fphi12)) & (e01 #? (tau 2 fphi12)) then (shufl pv10 pv01 (pi1 (d 3 fphi12)))
                            else (If (e10 #? (tau 1 fphi12)) & (e01 #? (tau 3 fphi12)) then (shufl pv10 (pi1 (d 2 fphi12)) pv01)
                                  else (If (e10 #? (tau 2 fphi12)) & (e01 #? (tau 1 fphi12)) then (shufl pv01 pv10 (pi1 (d 3 fphi12)))
                                        else (If (e10 #? (tau 3 fphi12)) & (e01 #? (tau 1 fphi12)) then (shufl pv01 (pi1 (d 2 fphi12)) pv10)
                                              else (If (e10 #? (tau 2 fphi12)) & (e01 #? (tau 3 fphi12)) then (shufl (pi1 (d 1 fphi12)) pv01 pv10)
                                                    else (If (e10 #? (tau 3 fphi12)) & (e01 #? (tau 2 fphi12)) then (shufl (pi1 (d 1 fphi12)) pv10 pv01)
                                                          else O)))))) in
                
                 let dv1 := (If (dist fphi12) & (pvchecks fphi12) then s1 else |_) in
                 let acc00 := (acc c00 t r0 t2) in
                 let acc11 := (acc c11 t r1 t3) in
                 let acc10 := (acc c10 t r0 t4) in
                 let acc01 := (acc c01 t r1 t5) in
                 let phi03:= phi02 ++[msg dv0] in
                 let phi13:= phi12 ++[msg dv1] in
                 let fphi03 := f (toListm phi03) in
                 let l00 := (If (bnlcheck c00 (N 0) fphi03) then (enc ((label c00 fphi03), (k0, THREE)) (pke 11) (er 9)) else O) in
                 let l11 := (If (bnlcheck c11 (N 1) fphi03) then (enc ((label c11 fphi03), (k1, THREE)) (pke 11) (er 10)) else O) in
                 let fphi13 := f (toListm phi13) in
                 let l10 := (If (bnlcheck c10 (N 0) fphi13) then (enc ((label c10 fphi13), (k0, THREE)) (pke 11) (er 9)) else O) in
                 let l01 := (If (bnlcheck c01 (N 1) fphi13) then (enc ((label c01 fphi13), (k1, THREE)) (pke 11) (er 10)) else O) in
                 let phi05:= phi03++[msg l00, msg l11] in   
                 let phi15:= phi13++[msg l10, msg l01] in
                 let fphi05 := f (toListm phi05) in
                 let fphi15 := f (toListm phi15) in
                 let do0 := (If (dist fphi05)& (pochecks fphi05)& (((isink k0 fphi05)&(isink k1 fphi05)) or (! ((isink k0 fphi05)or (isink k1 fphi05)))) then (sotrm fphi05) else |_) in
   let do1 := (If (dist fphi15)& (pochecks fphi15)& (((isink k0 fphi15)&(isink k1 fphi15)) or (! ((isink k0 fphi15)or (isink k1 fphi15)))) then (sotrm fphi15) else |_) in             
                 let t0s0 := (If acc00 & acc11 then ((e00, (e11, dv0)), (l00, (l11, do0))) else |_) in
                 let t1s1 := (If acc10 & acc01 then ((e10, (e01, dv1)), (l10, (l01, do1))) else |_) in
                 (occur_name_mylist 100 [msg t, msg t0, msg t1] = false) -> (Fresh (cons 0 nil) [msg t, msg t2, msg t3, msg t4, msg t5] = true) ->
                 [msg b00, msg b11, msg t0s0] ~ [msg b10, msg b01, msg t1s1].
           
Proof. intros.
pose proof(ext_blind_enc t t0 t1 []).
(**

Axiom extFuncapp_f1: forall n m b b' x x' y y' (z z': mylist n) g (g':_ -> mylist m), (z ++ [bol b, msg (If b then x else y)]) ~ (z' ++ [bol b', msg (If b' then x' else y')]) -> (z ++ [bol b, msg (If b then (x, (f (g (toListm (g' (z++[bol b] ++[msg x])))))) else |_)])~ (z' ++ [bol b', msg (If b' then (x', (f (g (toListm (g' (z'++[bol b'] ++[msg x'])))))) else |_)]).

Axiom extFuncapp_f2: forall n m b b' x x' y y' t t' (z z': mylist n) g (g':_ -> mylist m), (z ++ [bol b, msg (If b then (x, t) else y)]) ~ (z' ++ [bol b', msg (If b' then (x', t') else y')]) -> (z ++ [bol b, msg (If b then ((x, t), (f (g (toListm (g' (z++[bol b] ++[msg x, msg t])))))) else |_)])~ (z' ++ [bol b', msg (If b' then ((x', y'), (f (g (toListm (g' (z'++[bol b'] ++[msg x', msg t'])))))) else |_)]).

Axiom extFuncapp_f3: forall {n m} b b' x x' y y' t t' t1 t1' (z z': mylist n) g (g':_ -> mylist m), (z ++ [bol b, msg (If b then ((x, t), t1) else y)]) ~ (z' ++ [bol b', msg (If b' then ((x', t'), t1') else y')]) -> (z ++ [bol b, msg (If b then ((x, t), ((f (g (toListm (g' (z++[bol b] ++[msg x, msg t]))))), t1)) else |_)])~ (z' ++ [bol b', msg (If b' then ((x', y'), ((f (g (toListm (g' (z'++[bol b'] ++[msg x', msg t']))))), t1')) else |_)]).
Axiom extFuncapp_f4: forall {n m} b b' x x' y y' t t' t1 t1' t2 t2' (z z': mylist n) g (g':_ -> mylist m), (z ++ [bol b, msg (If b then ((x, t), (t1, t2)) else y)]) ~ (z' ++ [bol b', msg (If b' then ((x', t'), (t1', t2')) else y')]) -> (z ++ [bol b, msg (If b then ((x, t), ((f (g (toListm (g' (z ++[bol b, msg x, msg t]))))), (t1, t2))) else |_)])~ (z' ++ [bol b', msg (If b' then ((x', y'), ((f (g (toListm (g' (z' ++[bol b', msg x', msg t']))))), (t1', t2'))) else |_)]).
**)
assert( (| V0 (N 0) |) #? (| V1 (N 0) |) ## TRue ->
       Fresh [1; 2; 3; 4] [msg t, msg (V0 (N 0)), msg (V1 (N 0)), msg t0, msg t1] = true ->
       (^? (t) && true)%bool = true ->
       (Datatypes.length (distMvars [msg t0, msg t1]) =? 2)%nat = true ->
       (bVarMsg t0 ++ bVarMsg t1)%list = nil ->
       mVarMsg t0 = [5; 6] /\ mVarMsg t1 = [5; 6] ->
       (occur_name_msg 100 t || (occur_name_msg 100 t0 || (occur_name_msg 100 t1 || false)))%bool = false).
auto.
apply H7 in H8; auto. clear H7.
 fold r0 r1 in H8.
fold t2 t3 t4 t5 in H8.
fold v0 v1 k0 k1 in H8. fold c00 c11 c10 c01 in H8. fold t2 t3 t4 t5 in H8. fold acc00 acc11 acc10 acc01 in H8.
fold b00 b11 b10 b01 e00 e11 e10 e01 in H8.
fold e01 in H8. simpl in H8.
unfold t0s0, t1s1. unfold do0, do1. unfold fphi05, fphi15. simpl.
repeat unfold l00, l11, l10, l01. simpl.
(** These can be provable **)
Axiom andB_elim: forall b1 b2 t1 t2, (If b1 & b2 then t1 else t2) # (If b1 then (If b2 then t1 else t2) else t2).

Axiom red_k_reveal1: forall b1 b2 t, (If b1 then t else O) # (If b1 & b2 then t
                                                             else (If b1 & (! b2) then t
                                                                   else (If (! b1) & b2 then O else O))).

rewrite red_k_reveal1 with (b1:= bnlcheck c00 (N 0) fphi03) (b2:= (bnlcheck c11 (N 1) fphi03)).

Axiom red_k_reveal2: forall b1 b2 t, (If b2 then t else O) # (If b1 & b2 then t
                                                             else (If b1 & (! b2) then O
                                                                   else (If (! b1) & b2 then t else O))).



repeat rewrite red_k_reveal2 with (b1:= bnlcheck c00 (N 0) fphi03) (b2:= (bnlcheck c11 (N 1) fphi03)).
simpl.
(*Axiom red_k_reveal_r: forall b1 b2 t, (If b2 then t else O) # (If b1 & b2 then t
                                                             else (If b1 & (! b2) then O
                                                                   else (If (! b1) & b2 then t else O))). *) simpl.
repeat rewrite red_k_reveal1 with (b1:= bnlcheck c10 (N 0) fphi13) (b2:= (bnlcheck c01 (N 1) fphi13)).
repeat rewrite red_k_reveal2 with (b1:= bnlcheck c10 (N 0) fphi13) (b2:= (bnlcheck c01 (N 1) fphi13)). 



Axiom dupAcc: forall b b1 b2 b3 e00 e11 dv0 b00 b11 k0 k1 t1 t2 t3 t4 t5 t6 t7 t8, (let l00:= If b1 then t1 else (If b2 then t2 else (If b3 then t3 else t4)) in
                                                                         let l11:= If b1 then t5 else (If b2 then t6 else (If b3 then t7 else t8)) in
                                                                         (If b then (e00, (e11, dv0), (l00, (l11, If (dist (f [b00; b11; e00; e11; dv0; l00; l11])) &
                 (pochecks (f [b00; b11; e00; e11; dv0; l00; l11])) &
                 ((isink k0 (f [b00; b11; e00; e11; dv0; l00; l11])) & (isink k1 (f [b00; b11; e00; e11; dv0; l00; l11]))) or
                 ! ((isink k0 (f [b00; b11; e00; e11; dv0; l00; l11])) or (isink k1 (f [b00; b11; e00; e11; dv0; l00; l11])))
                 then sotrm (f [b00; b11; e00; e11; dv0; l00; l11]) 
                                                                                                             else |_))) else |_)) # (let l00:= If b&b1 then t1 else (If b&b2 then t2 else (If b&b3 then t3 else t4)) in
  let l11:= If b&b1 then t5 else (If b&b2 then t6 else (If b&b3 then t7 else t8)) in                                                                                                                                       (If b then (e00, (e11, dv0), (l00, (l11,  If (dist (f [b00; b11; e00; e11; dv0; l00; l11])) &
                 (pochecks (f [b00; b11; e00; e11; dv0; l00; l11])) &
                 ((isink k0 (f [b00; b11; e00; e11; dv0; l00; l11])) & (isink k1 (f [b00; b11; e00; e11; dv0; l00; l11]))) or
                 ! ((isink k0 (f [b00; b11; e00; e11; dv0; l00; l11])) or (isink k1 (f [b00; b11; e00; e11; dv0; l00; l11])))
                 then sotrm (f [b00; b11; e00; e11; dv0; l00; l11])
                                                                                                             else |_))) else |_)).
Axiom extIfmr: forall b b' b00 b11 k0 k1 e00 e11 dv0 t1 t2 t3 t4, (let l00:= If b' then t1 else t2 in
let l11:= If b' then t3 else t4 in
(If b then (e00, (e11, dv0), (l00, (l11,  If (dist (f [b00; b11; e00; e11; dv0; l00; l11])) &
                 (pochecks (f [b00; b11; e00; e11; dv0; l00; l11])) &
                 ((isink k0 (f [b00; b11; e00; e11; dv0; l00; l11])) & (isink k1 (f [b00; b11; e00; e11; dv0; l00; l11]))) or
                 ! ((isink k0 (f [b00; b11; e00; e11; dv0; l00; l11])) or (isink k1 (f [b00; b11; e00; e11; dv0; l00; l11])))
                 then sotrm (f [b00; b11; e00; e11; dv0; l00; l11]) 
                 else |_))) else |_)) #  (let l00:= t1 in
                                         let l11:= t3 in
                                         let l00':= t2 in
                                         let l11':= t4 in
 (If b' then (If b then (e00, (e11, dv0), (l00, (l11, If (dist (f [b00; b11; e00; e11; dv0; l00; l11])) &
                 (pochecks (f [b00; b11; e00; e11; dv0; l00; l11])) &
                 ((isink k0 (f [b00; b11; e00; e11; dv0; l00; l11])) & (isink k1 (f [b00; b11; e00; e11; dv0; l00; l11]))) or
                 ! ((isink k0 (f [b00; b11; e00; e11; dv0; l00; l11])) or (isink k1 (f [b00; b11; e00; e11; dv0; l00; l11])))
                 then sotrm (f [b00; b11; e00; e11; dv0; l00; l11]) 
                 else |_))) else |_) else (If b then (e00, (e11, dv0), (l00', (l11', If (dist (f [b00; b11; e00; e11; dv0; l00'; l11'])) &
                 (pochecks (f [b00; b11; e00; e11; dv0; l00'; l11'])) &
                 ((isink k0 (f [b00; b11; e00; e11; dv0; l00'; l11'])) & (isink k1 (f [b00; b11; e00; e11; dv0; l00'; l11']))) or
                 ! ((isink k0 (f [b00; b11; e00; e11; dv0; l00'; l11'])) or (isink k1 (f [b00; b11; e00; e11; dv0; l00'; l11'])))
                 then sotrm (f [b00; b11; e00; e11; dv0; l00'; l11']) 
                 else |_))) else |_))).
 
 rewrite dupAcc with (b:= acc00&acc11).  
rewrite dupAcc with (b:= acc10 & acc01). 
rewrite extIfmr with (b:= (acc00) & acc11).
rewrite extIfmr with (b:= (acc10) & acc01). simpl.
apply IFBRANCH_M1 with (ml1:= [msg b00, msg b11]) (ml2:= [msg b10, msg b01]). simpl.


apply extFuncapp with (b:= acc00& acc11) (b':= acc10&acc01) (z:= [msg b00, msg b11]) (z':= [msg b10, msg b01]) (f:= (fun z b x => (x, (f (toListm (z ++ [msg (pi1 (pi1 (pi1 x))), msg (pi2 (pi1 (pi1 x)))])))))) in H8.
simpl in H8. repeat rewrite proj1 in H8. repeat rewrite proj2 in H8.


apply extFuncapp with (b:= acc00& acc11) (b':= acc10&acc01) (z:= [msg b00, msg b11]) (z':= [msg b10, msg b01]) (f:= (fun z b x =>
                                                                                                                       (x, If (dist (pi2 x)) & (pvchecks (pi2 x))
                 then If (((pi1 (pi1 (pi1 (pi1 x))))) #? (tau 1 (pi2 x))) & ((pi2 (pi1 (pi1 (pi1 x))))) #? (tau 2 (pi2 x))
                         then shufl (pi1 (pi2 (pi1 x)))
                                (pi2 (pi2 (pi1 x)))
                                (pi1 (d 3 (pi2 x))) 
                         else If (((pi1 (pi1 (pi1 (pi1 x))))) #? (tau 1 (pi2 x))) &
                                 ((pi2 (pi1 (pi1 (pi1 x))))) #? (tau 3 (pi2 x))
                                 then shufl (pi1 (pi2 (pi1 x)))
                                        (pi1 (d 2 (pi2 x)))
                                        (pi2 (pi2 (pi1 x))) 
                                 else If (((pi1 (pi1 (pi1 (pi1 x))))) #? (tau 2 (pi2 x))) &
                                         ((pi2 (pi1 (pi1 (pi1 x))))) #? (tau 1 (pi2 x))
                                         then shufl
                                                (pi2 (pi2 (pi1 x)))
                                                (pi1 (pi2 (pi1 x)))
                                                (pi1 (d 3 (pi2 x))) 
                                         else If (((pi1 (pi1 (pi1 (pi1 x))))) #? (tau 3 (pi2 x))) &
                                                 ((pi2 (pi1 (pi1 (pi1 x))))) #? (tau 1 (pi2 x))
                                                 then 
                                                 shufl
                                                 (pi2 (pi2 (pi1 x)))
                                                 (pi1 (d 2 (pi2 x)))
                                                 (pi1 (pi2 (pi1 x))) 
                                                 else 
                                                 If (((pi1 (pi1 (pi1 (pi1 x))))) #? (tau 2 (pi2 x)))
                                                 & ((pi2 (pi1 (pi1 (pi1 x))))) #? (tau 3 (pi2 x))
                                                 then 
                                                 shufl 
                                                 (pi1 (d 1 (pi2 x)))
                                                 (pi2 (pi2 (pi1 x)))
                                                 (pi1 (pi2 (pi1 x))) 
                                                 else 
                                                 If (((pi1 (pi1 (pi1 (pi1 x))))) #? (tau 3 (pi2 x)))
                                                 & ((pi2 (pi1 (pi1 (pi1 x))))) #? (tau 2 (pi2 x))
                                                 then 
                                                 shufl 
                                                 (pi1 (d 1 (pi2 x)))
                                                 (pi1 (pi2 (pi1 x)))
                                                 (pi2 (pi2 (pi1 x))) 
                                                 else O 
                                                                                                                        else |_))) in H8.  repeat unfold dist, d, pvchecks in H8.

Axiom tau_cong: forall n n' t t', n = n' -> t # t' ->  (tau n t) # (tau n' t').
Add Parametric Morphism: (@tau) with
      signature eq ==> EQm ==> EQm as tau_mor.
Proof. intros. apply tau_cong; auto.  Qed. 
rewrite proj1 in H8. repeat  try rewrite proj2, proj1 in H8.
repeat rewrite proj1 in H8. 
(** to reduce the size of the terms **)
assert ((If ((e10) #? (tau 1 (f [b10; b01; e10; e01]))) & (e01) #? (tau 2 (f [b10; b01; e10; e01]))
                              then shufl (c01, (ub c01 t r1 t5, N 1)) (c10, (ub c10 t r0 t4, N 0))
                                     (pi1 (dec (tau 3 (f [b10; b01; e10; e01])) (ske 11))) 
                              else If ((e10) #? (tau 1 (f [b10; b01; e10; e01]))) & (e01) #? (tau 3 (f [b10; b01; e10; e01]))
                                      then shufl (c01, (ub c01 t r1 t5, N 1))
                                             (pi1 (dec (tau 2 (f [b10; b01; e10; e01])) (ske 11))) (c10, (ub c10 t r0 t4, N 0)) 
                                      else If ((e10) #? (tau 2 (f [b10; b01; e10; e01]))) &
                                              (e01) #? (tau 1 (f [b10; b01; e10; e01]))
                                              then shufl (c10, (ub c10 t r0 t4, N 0)) (c01, (ub c01 t r1 t5, N 1))
                                                     (pi1 (dec (tau 3 (f [b10; b01; e10; e01])) (ske 11))) 
                                              else If ((e10) #? (tau 3 (f [b10; b01; e10; e01]))) &
                                                      (e01) #? (tau 1 (f [b10; b01; e10; e01]))
                                                      then shufl (c10, (ub c10 t r0 t4, N 0))
                                                             (pi1 (dec (tau 2 (f [b10; b01; e10; e01])) (ske 11)))
                                                             (c01, (ub c01 t r1 t5, N 1)) 
                                                      else If ((e10) #? (tau 2 (f [b10; b01; e10; e01]))) &
                                                              (e01) #? (tau 3 (f [b10; b01; e10; e01]))
                                                              then shufl (pi1 (dec (tau 1 (f [b10; b01; e10; e01])) (ske 11)))
                                                                     (c10, (ub c10 t r0 t4, N 0)) (c01, (ub c01 t r1 t5, N 1)) 
                                                              else If ((e10) #? (tau 3 (f [b10; b01; e10; e01]))) &
                                                                      (e01) #? (tau 2 (f [b10; b01; e10; e01]))
                                                                      then shufl
                                                                             (pi1 (dec (tau 1 (f [b10; b01; e10; e01])) (ske 11)))
                                                                             (c01, (ub c01 t r1 t5, N 1))
                                                                             (c10, (ub c10 t r0 t4, N 0)) 
         else O )# s1).
unfold s1. unfold pv10, pv01.  simpl.
rewrite shuffle3 with (t1:= (c01, (ub c01 t r1 t5, N 1))) (t2:= (c10, (ub c10 t r0 t4, N 0))).  
rewrite shuffle6 with (t1:=  (c01, (ub c01 t r1 t5, N 1))) (t3:= (c10, (ub c10 t r0 t4, N 0))).
assert ((If ((e10) #? (pi1 (pi2 (f [b10; b01; e10; e01])))) & (e01) #? (pi1 (f [b10; b01; e10; e01]))
                      then shufl (c10, (ub c10 t r0 t4, N 0)) (c01, (ub c01 t r1 t5, N 1))
                             (pi1 (dec (pi2 (pi2 (f [b10; b01; e10; e01]))) (ske 11))) 
                      else If ((e10) #? (pi2 (pi2 (f [b10; b01; e10; e01])))) & (e01) #? (pi1 (f [b10; b01; e10; e01]))
                              then shufl (c10, (ub c10 t r0 t4, N 0)) (pi1 (dec (pi1 (pi2 (f [b10; b01; e10; e01]))) (ske 11)))
                                     (c01, (ub c01 t r1 t5, N 1)) 
                              else If ((e10) #? (pi1 (pi2 (f [b10; b01; e10; e01])))) &
                                      (e01) #? (pi2 (pi2 (f [b10; b01; e10; e01])))
                                      then shufl (pi1 (dec (pi1 (f [b10; b01; e10; e01])) (ske 11))) (c10, (ub c10 t r0 t4, N 0))
                                             (c01, (ub c01 t r1 t5, N 1)) 
                                      else If ((e10) #? (pi2 (pi2 (f [b10; b01; e10; e01])))) &
                                              (e01) #? (pi1 (pi2 (f [b10; b01; e10; e01])))
                                              then shufl (pi1 (dec (pi1 (f [b10; b01; e10; e01])) (ske 11)))
                                                     (c01, (ub c01 t r1 t5, N 1)) (c10, (ub c10 t r0 t4, N 0)) 
                                              else O) # (If ((e10) #? (pi1 (pi2 fphi12))) & (e01) #? (pi1 fphi12)
                        then shufl (c01, (ub c01 t r1 t5, N 1)) (c10, (ub c10 t r0 t4, N 0)) (pi1 (d 3 fphi12)) 
                        else If ((e10) #? (pi2 (pi2 fphi12))) & (e01) #? (pi1 fphi12)
                                then shufl (c01, (ub c01 t r1 t5, N 1)) (pi1 (d 2 fphi12)) (c10, (ub c10 t r0 t4, N 0)) 
                                else If ((e10) #? (pi1 (pi2 fphi12))) & (e01) #? (pi2 (pi2 fphi12))
                                        then shufl (pi1 (d 1 fphi12)) (c01, (ub c01 t r1 t5, N 1)) (c10, (ub c10 t r0 t4, N 0)) 
                                        else If ((e10) #? (pi2 (pi2 fphi12))) & (e01) #? (pi1 (pi2 fphi12))
                                                then shufl (pi1 (d 1 fphi12)) (c10, (ub c10 t r0 t4, N 0))
                                                       (c01, (ub c01 t r1 t5, N 1)) 
                                                else O)).

rewrite shuffle3 with (t1:= (c10, (ub c10 t r0 t4, N 0))) (t2:= (c01, (ub c01 t r1 t5, N 1))) (t3:= (pi1 (dec (pi2 (pi2 (f [b10; b01; e10; e01]))) (ske 11))) ).
rewrite shuffle6 with (t1:= (c10, (ub c10 t r0 t4, N 0))) (t3:= (c01, (ub c01 t r1 t5, N 1))). 
assert((If ((e10) #? (pi1 (pi2 (f [b10; b01; e10; e01])))) & (e01) #? (pi2 (pi2 (f [b10; b01; e10; e01])))
                      then shufl (pi1 (dec (pi1 (f [b10; b01; e10; e01])) (ske 11))) (c10, (ub c10 t r0 t4, N 0))
                             (c01, (ub c01 t r1 t5, N 1)) 
                      else If ((e10) #? (pi2 (pi2 (f [b10; b01; e10; e01])))) & (e01) #? (pi1 (pi2 (f [b10; b01; e10; e01])))
                              then shufl (pi1 (dec (pi1 (f [b10; b01; e10; e01])) (ske 11))) (c01, (ub c01 t r1 t5, N 1))
                                     (c10, (ub c10 t r0 t4, N 0)) 
                              else O) # (If ((e10) #? (pi1 (pi2 fphi12))) & (e01) #? (pi2 (pi2 fphi12))
                        then shufl (pi1 (d 1 fphi12)) (c01, (ub c01 t r1 t5, N 1)) (c10, (ub c10 t r0 t4, N 0)) 
                        else If ((e10) #? (pi2 (pi2 fphi12))) & (e01) #? (pi1 (pi2 fphi12))
                                then shufl (pi1 (d 1 fphi12)) (c10, (ub c10 t r0 t4, N 0)) (c01, (ub c01 t r1 t5, N 1)) 
                                else O)).

rewrite shuffle2 with (t2:= (c10, (ub c10 t r0 t4, N 0))) (t3:=  (c01, (ub c01 t r1 t5, N 1)) ).
assert((If ((e10) #? (pi2 (pi2 fphi12))) & (e01) #? (pi1 (pi2 fphi12))
                then shufl (pi1 (d 1 fphi12)) (c10, (ub c10 t r0 t4, N 0)) (c01, (ub c01 t r1 t5, N 1)) 
                else O) # (If ((e10) #? (pi2 (pi2 (f [b10; b01; e10; e01])))) & (e01) #? (pi1 (pi2 (f [b10; b01; e10; e01])))
              then shufl (pi1 (dec (pi1 (f [b10; b01; e10; e01])) (ske 11))) (c01, (ub c01 t r1 t5, N 1))
                     (c10, (ub c10 t r0 t4, N 0)) 
              else O)).
rewrite shuffle2 with (t2:= (c10, (ub c10 t r0 t4, N 0))) (t3:=  (c01, (ub c01 t r1 t5, N 1)) ).
reflexivity. 
repeat try (rewrite H7;try reflexivity). rewrite H7. reflexivity. rewrite H7. reflexivity.
rewrite H7 in H8. simpl in H8.

clear H7.
(***************************)
assert([msg b00, msg b11, bol (acc00) & acc11,
       msg
         (If (acc00) & acc11
             then (e00, e11, (c00, k0, (c11, k1)),
                  (c00, (ub c00 t r0 t2, N 0), (c11, (ub c11 t r1 t3, N 1))),
                  fphi02,
                 dv0) 
             else |_)]~ [msg b10, msg b01, bol (acc10) & acc01,
       msg
         (If (acc10) & acc01
             then (e10, e01, (c01, k1, (c10, k0)),
                  (c01, (ub c01 t r1 t5, N 1), (c10, (ub c10 t r0 t4, N 0))),
                  fphi12,
                 dv1) 
             else |_)]).
assumption. clear H8.

(** construction phi3 using extfuncapp **)
unfold fphi03. simpl. 
apply extFuncapp with (b:= acc00& acc11) (b':= acc10&acc01) (z:= [msg b00, msg b11]) (z':= [msg b10, msg b01]) (f:= (fun z b x =>
                                                                                                                       (x, (f (toListm (z ++ [msg (pi1 (pi1 (pi1 (pi1 (pi1 x))))), msg (pi2 (pi1 (pi1 (pi1 (pi1 x))))), msg (pi2 x)])))))) in H7.
simpl in H7.
rewrite proj1 in H7. repeat rewrite proj2 in H7.
repeat rewrite proj1 in H7. repeat rewrite proj2 in H7.
Axiom orB_cong: forall b1 b2 b3 b4, b1 ## b2 -> b3 ## b4 -> (IF b1 then TRue else b3) ## (IF b2 then TRue else b4).
Add Parametric Morphism: (@orB) with
      signature EQb ==> EQb ==> EQb as orB_mor.
Proof. intros. apply orB_cong; auto.  Qed.

Axiom extFuncappb: forall n b b' x x' y y' (z z': mylist n) (f : (mylist n) -> Bool -> message-> Bool), (z ++ [bol b, msg (If b then x else y)]) ~ (z' ++ [bol b', msg (If b' then x' else y')]) -> (z ++ [bol b, msg (If b then x else y), bol (IF b then (f z b x) else FAlse)])~ (z' ++ [bol b', msg (If b' then x' else y'), bol (IF b' then (f z' b' x') else FAlse)]).

repeat rewrite proj1. repeat rewrite proj2, proj1.
 
apply extFuncapp with (b:= acc00& acc11) (b':= acc10&acc01) (z:= [msg b00, msg b11]) (z':= [msg b10, msg b01])
                      (f:= (fun z b x => (x, ((enc (label (pi1 (tau 1 (pi2 (pi1 (pi1 (pi1 (pi1 x))))))) (pi2 x), ((pi2 (tau 1 (pi2 (pi1 (pi1 (pi1 (pi1 x))))))), THREE)) (pke 11) (er 9)), (enc (label (tau 2 (pi2 (pi1 (pi1 (pi1 (pi1 x)))))) (pi2 x), ((tau 3 (pi2 (pi1 (pi1 (pi1 (pi1 x)))))), THREE)) (pke 11) (er 10)))))) in H7. simpl in H7.
repeat unfold label, isin in H7.
repeat rewrite proj1 in H7. repeat  try rewrite proj2, proj1 in H7.  repeat rewrite proj1 in H7.   repeat rewrite proj2 in H7.
repeat rewrite proj1 in H7.
repeat rewrite proj2 in H7.
Axiom aply_cca2_twice: forall n (z z':mylist n), z ~ z'.
assert(fapp: [msg b10, msg b01, bol (acc10) & acc01,
       msg
         (If (acc10) & acc01
             then (e10, e01, (c01, k1, (c10, k0)), (c01, (ub c01 t r1 t5, N 1), (c10, (ub c10 t r0 t4, N 0))), fphi12, dv1,
                  f [b10; b01; e10; e01; dv1],
                  ((enc (If (c01) #? (tau 2 (pi2 (tau 1 (f [b10; b01; e10; e01; dv1]))))
                        then pi1 (tau 1 (f [b10; b01; e10; e01; dv1])) 
                        else If (c01) #? (tau 2 (pi2 (tau 2 (f [b10; b01; e10; e01; dv1]))))
                                then pi1 (tau 2 (f [b10; b01; e10; e01; dv1])) 
                                else If (c01) #? (tau 2 (pi2 (tau 3 (f [b10; b01; e10; e01; dv1]))))
                                        then pi1 (tau 3 (f [b10; b01; e10; e01; dv1])) 
                                        else O, (k1, THREE)) (pke 11) (er 9)),
                  (enc (If (c10) #? (tau 2 (pi2 (tau 1 (f [b10; b01; e10; e01; dv1]))))
                       then pi1 (tau 1 (f [b10; b01; e10; e01; dv1])) 
                       else If (c10) #? (tau 2 (pi2 (tau 2 (f [b10; b01; e10; e01; dv1]))))
                               then pi1 (tau 2 (f [b10; b01; e10; e01; dv1])) 
                               else If (c10) #? (tau 2 (pi2 (tau 3 (f [b10; b01; e10; e01; dv1]))))
                                       then pi1 (tau 3 (f [b10; b01; e10; e01; dv1])) 
                                       else O, (k0, THREE)) (pke 11) (er 10)))) 
             else |_)] ~[msg b10, msg b01, bol (acc10) & acc01,
       msg
         (If (acc10) & acc01
             then (e10, e01, (c01, k1, (c10, k0)), (c01, (ub c01 t r1 t5, N 1), (c10, (ub c10 t r0 t4, N 0))), fphi12, dv1,
                  f [b10; b01; e10; e01; dv1],
                  ((enc (label c10 fphi13, (k0, THREE)) (pke 11) (er 9)), (enc (label c01 fphi13, (k1, THREE)) (pke 11) (er 10))))
             else |_)]).
apply aply_cca2_twice.

assert( [msg b00, msg b11, bol (acc00) & acc11,
        msg
          (If (acc00) & acc11
              then (e00, e11, (c00, k0, (c11, k1)), (c00, (ub c00 t r0 t2, N 0), (c11, (ub c11 t r1 t3, N 1))), fphi02, dv0,
                   f [b00; b11; e00; e11; dv0], ((enc (label c00 (f [b00; b11; e00; e11; dv0]), (k0, THREE)) (pke 11) (er 9)), (enc (label c11 (f [b00; b11; e00; e11; dv0]), (k1, THREE)) (pke 11) (er 10)))) else |_)] ~ [msg b10, msg b01, bol (acc10) & acc01,
       msg
         (If (acc10) & acc01
             then (e10, e01, (c01, k1, (c10, k0)), (c01, (ub c01 t r1 t5, N 1), (c10, (ub c10 t r0 t4, N 0))), fphi12, dv1,
                  f [b10; b01; e10; e01; dv1],
                  ((enc (label c10 fphi13, (k0, THREE)) (pke 11) (er 9)), (enc (label c01 fphi13, (k1, THREE)) (pke 11) (er 10))))
             else |_)]).
apply EQI_trans with (ml2:= [msg b10, msg b01, bol (acc10) & acc01,
       msg
         (If (acc10) & acc01
             then (e10, e01, (c01, k1, (c10, k0)), (c01, (ub c01 t r1 t5, N 1), (c10, (ub c10 t r0 t4, N 0))), fphi12, dv1,
                  f [b10; b01; e10; e01; dv1],
                  ((enc (If (c01) #? (tau 2 (pi2 (tau 1 (f [b10; b01; e10; e01; dv1]))))
                        then pi1 (tau 1 (f [b10; b01; e10; e01; dv1])) 
                        else If (c01) #? (tau 2 (pi2 (tau 2 (f [b10; b01; e10; e01; dv1]))))
                                then pi1 (tau 2 (f [b10; b01; e10; e01; dv1])) 
                                else If (c01) #? (tau 2 (pi2 (tau 3 (f [b10; b01; e10; e01; dv1]))))
                                        then pi1 (tau 3 (f [b10; b01; e10; e01; dv1])) 
                                        else O, (k1, THREE)) (pke 11) (er 9)),
                  (enc (If (c10) #? (tau 2 (pi2 (tau 1 (f [b10; b01; e10; e01; dv1]))))
                       then pi1 (tau 1 (f [b10; b01; e10; e01; dv1])) 
                       else If (c10) #? (tau 2 (pi2 (tau 2 (f [b10; b01; e10; e01; dv1]))))
                               then pi1 (tau 2 (f [b10; b01; e10; e01; dv1])) 
                               else If (c10) #? (tau 2 (pi2 (tau 3 (f [b10; b01; e10; e01; dv1]))))
                                       then pi1 (tau 3 (f [b10; b01; e10; e01; dv1])) 
                                       else O, (k0, THREE)) (pke 11) (er 10)))) 
             else |_)]); auto.
clear H7 fapp. 

repeat rewrite proj1.   
apply extFuncappb with (b:= acc00& acc11) (b':= acc10&acc01) (z:= [msg b00, msg b11]) (z':= [msg b10, msg b01])
                       (f:= (fun z b x => (bnlcheck (tau 1 (pi1  (pi2  (pi1 (pi1 (pi1 (tau 1 x))))))) (tau 3 (pi1  (pi2  (pi1 (pi1 (pi1 (tau 1 x))))))) (pi2 (tau 1 x))) & (bnlcheck (tau 1 (pi2  (pi2  (pi1 (pi1 (pi1 (tau 1 x))))))) (tau 3 (pi2  (pi2  (pi1 (pi1 (pi1 (tau 1 x))))))) (pi2 (tau 1 x))))) in H8.

repeat unfold bnlcheck, ncheck, bcheck, label, isin in H8.
rewrite ?proj1 in H8.
rewrite ?tau1 in H8. rewrite ?proj2 in H8. rewrite ?tau1 in H8.
rewrite ?tau2 in H8. rewrite ?tau3 in H8.  simpl in H8.
restr_swap_in 4 5 H8. restr_swap_in 3 4 H8.


rewrite ?proj1.                 
  Definition dropone' {n:nat} (m:mylist n):(mylist (pred n)):=
  match m with 
    | [] => []
    | Cons _ _ h m1 => m1
  end. 
  Eval compute in dropone' [msg b10, msg b01, msg O]. 
apply extFuncapp with  (b:= acc00& acc11) (b':= acc10&acc01) (z:= [msg b00, msg b11, bol (IF (acc00) & acc11
           then ((((c00) #? (pi1 (pi2 (pi1 (f [b00; b11; e00; e11; dv0]))))) or
                  ((c00) #? (pi1 (pi2 (pi1 (pi2 (f [b00; b11; e00; e11; dv0])))))) or
                  (c00) #? (pi1 (pi2 (pi2 (pi2 (f [b00; b11; e00; e11; dv0])))))) &
                 ((| If (c00) #? (pi1 (pi2 (pi2 (pi1 (f [b00; b11; e00; e11; dv0])))))
                        then pi1 (pi1 (f [b00; b11; e00; e11; dv0])) 
                        else If (c00) #? (pi1 (pi2 (pi2 (pi1 (pi2 (f [b00; b11; e00; e11; dv0]))))))
                                then pi1 (pi1 (pi2 (f [b00; b11; e00; e11; dv0]))) 
                                else If (c00) #? (pi1 (pi2 (pi2 (pi2 (pi2 (f [b00; b11; e00; e11; dv0]))))))
                                        then pi1 (pi2 (pi2 (f [b00; b11; e00; e11; dv0]))) 
                                        else O |) #? lbl) &
                 ((N 0) #? (pi2 (pi2 (pi2 (pi1 (f [b00; b11; e00; e11; dv0])))))) or
                 ((N 0) #? (pi2 (pi2 (pi2 (pi1 (pi2 (f [b00; b11; e00; e11; dv0]))))))) or
                 (N 0) #? (pi2 (pi2 (pi2 (pi2 (pi2 (f [b00; b11; e00; e11; dv0]))))))) &
                (((c11) #? (pi1 (pi2 (pi1 (f [b00; b11; e00; e11; dv0]))))) or
                 ((c11) #? (pi1 (pi2 (pi1 (pi2 (f [b00; b11; e00; e11; dv0])))))) or
                 (c11) #? (pi1 (pi2 (pi2 (pi2 (f [b00; b11; e00; e11; dv0])))))) &
                ((| If (c11) #? (pi1 (pi2 (pi2 (pi1 (f [b00; b11; e00; e11; dv0])))))
                       then pi1 (pi1 (f [b00; b11; e00; e11; dv0])) 
                       else If (c11) #? (pi1 (pi2 (pi2 (pi1 (pi2 (f [b00; b11; e00; e11; dv0]))))))
                               then pi1 (pi1 (pi2 (f [b00; b11; e00; e11; dv0]))) 
                               else If (c11) #? (pi1 (pi2 (pi2 (pi2 (pi2 (f [b00; b11; e00; e11; dv0]))))))
                                       then pi1 (pi2 (pi2 (f [b00; b11; e00; e11; dv0]))) 
                                       else O |) #? lbl) &
                ((N 1) #? (pi2 (pi2 (pi2 (pi1 (f [b00; b11; e00; e11; dv0])))))) or
                ((N 1) #? (pi2 (pi2 (pi2 (pi1 (pi2 (f [b00; b11; e00; e11; dv0]))))))) or
                (N 1) #? (pi2 (pi2 (pi2 (pi2 (pi2 (f [b00; b11; e00; e11; dv0])))))) else FAlse)]) (z':= [msg b10, msg b01, bol (IF (acc10) & acc01
          then ((((c01) #? (pi1 (pi2 (pi1 (f [b10; b01; e10; e01; dv1]))))) or
                 ((c01) #? (pi1 (pi2 (pi1 (pi2 (f [b10; b01; e10; e01; dv1])))))) or
                 (c01) #? (pi1 (pi2 (pi2 (pi2 (f [b10; b01; e10; e01; dv1])))))) &
                ((| If (c01) #? (pi1 (pi2 (pi2 (pi1 (f [b10; b01; e10; e01; dv1])))))
                       then pi1 (pi1 (f [b10; b01; e10; e01; dv1])) 
                       else If (c01) #? (pi1 (pi2 (pi2 (pi1 (pi2 (f [b10; b01; e10; e01; dv1]))))))
                               then pi1 (pi1 (pi2 (f [b10; b01; e10; e01; dv1]))) 
                               else If (c01) #? (pi1 (pi2 (pi2 (pi2 (pi2 (f [b10; b01; e10; e01; dv1]))))))
                                       then pi1 (pi2 (pi2 (f [b10; b01; e10; e01; dv1]))) 
                                       else O |) #? lbl) &
                ((N 1) #? (pi2 (pi2 (pi2 (pi1 (f [b10; b01; e10; e01; dv1])))))) or
                ((N 1) #? (pi2 (pi2 (pi2 (pi1 (pi2 (f [b10; b01; e10; e01; dv1]))))))) or
                (N 1) #? (pi2 (pi2 (pi2 (pi2 (pi2 (f [b10; b01; e10; e01; dv1]))))))) &
               (((c10) #? (pi1 (pi2 (pi1 (f [b10; b01; e10; e01; dv1]))))) or
                ((c10) #? (pi1 (pi2 (pi1 (pi2 (f [b10; b01; e10; e01; dv1])))))) or
                (c10) #? (pi1 (pi2 (pi2 (pi2 (f [b10; b01; e10; e01; dv1])))))) &
               ((| If (c10) #? (pi1 (pi2 (pi2 (pi1 (f [b10; b01; e10; e01; dv1])))))
                      then pi1 (pi1 (f [b10; b01; e10; e01; dv1])) 
                      else If (c10) #? (pi1 (pi2 (pi2 (pi1 (pi2 (f [b10; b01; e10; e01; dv1]))))))
                              then pi1 (pi1 (pi2 (f [b10; b01; e10; e01; dv1]))) 
                              else If (c10) #? (pi1 (pi2 (pi2 (pi2 (pi2 (f [b10; b01; e10; e01; dv1]))))))
                                      then pi1 (pi2 (pi2 (f [b10; b01; e10; e01; dv1]))) 
                                      else O |) #? lbl) &
               ((N 0) #? (pi2 (pi2 (pi2 (pi1 (f [b10; b01; e10; e01; dv1])))))) or
               ((N 0) #? (pi2 (pi2 (pi2 (pi1 (pi2 (f [b10; b01; e10; e01; dv1]))))))) or
               (N 0) #? (pi2 (pi2 (pi2 (pi2 (pi2 (f [b10; b01; e10; e01; dv1])))))) else FAlse)]) (f:= (fun z b x => (x, (f (toListm (reverse (dropone (reverse z)) ++ [msg (pi1 (pi1 (pi1 (pi1 (pi1 (pi1 (tau 1 x))))))), msg (pi2 (pi1 (pi1 (pi1 (pi1 (pi1 (tau 1 x))))))), msg (pi2 (pi1 (tau 1 x))), msg (tau 2 x), msg (tau 3 x)])))))) in H8.
simpl in H8.
 rewrite ?proj1 in H8.
rewrite ?tau1 in H8.
rewrite ?tau2 in H8.
rewrite ?tau3 in H8.
rewrite ?proj2 in H8. rewrite ?proj1 in H8.

apply extFuncapp with  (b:= acc00& acc11) (b':= acc10&acc01) (z:= [msg b00, msg b11, bol (IF (acc00) & acc11
           then ((((c00) #? (pi1 (pi2 (pi1 (f [b00; b11; e00; e11; dv0]))))) or
                  ((c00) #? (pi1 (pi2 (pi1 (pi2 (f [b00; b11; e00; e11; dv0])))))) or
                  (c00) #? (pi1 (pi2 (pi2 (pi2 (f [b00; b11; e00; e11; dv0])))))) &
                 ((| If (c00) #? (pi1 (pi2 (pi2 (pi1 (f [b00; b11; e00; e11; dv0])))))
                        then pi1 (pi1 (f [b00; b11; e00; e11; dv0])) 
                        else If (c00) #? (pi1 (pi2 (pi2 (pi1 (pi2 (f [b00; b11; e00; e11; dv0]))))))
                                then pi1 (pi1 (pi2 (f [b00; b11; e00; e11; dv0]))) 
                                else If (c00) #? (pi1 (pi2 (pi2 (pi2 (pi2 (f [b00; b11; e00; e11; dv0]))))))
                                        then pi1 (pi2 (pi2 (f [b00; b11; e00; e11; dv0]))) 
                                        else O |) #? lbl) &
                 ((N 0) #? (pi2 (pi2 (pi2 (pi1 (f [b00; b11; e00; e11; dv0])))))) or
                 ((N 0) #? (pi2 (pi2 (pi2 (pi1 (pi2 (f [b00; b11; e00; e11; dv0]))))))) or
                 (N 0) #? (pi2 (pi2 (pi2 (pi2 (pi2 (f [b00; b11; e00; e11; dv0]))))))) &
                (((c11) #? (pi1 (pi2 (pi1 (f [b00; b11; e00; e11; dv0]))))) or
                 ((c11) #? (pi1 (pi2 (pi1 (pi2 (f [b00; b11; e00; e11; dv0])))))) or
                 (c11) #? (pi1 (pi2 (pi2 (pi2 (f [b00; b11; e00; e11; dv0])))))) &
                ((| If (c11) #? (pi1 (pi2 (pi2 (pi1 (f [b00; b11; e00; e11; dv0])))))
                       then pi1 (pi1 (f [b00; b11; e00; e11; dv0])) 
                       else If (c11) #? (pi1 (pi2 (pi2 (pi1 (pi2 (f [b00; b11; e00; e11; dv0]))))))
                               then pi1 (pi1 (pi2 (f [b00; b11; e00; e11; dv0]))) 
                               else If (c11) #? (pi1 (pi2 (pi2 (pi2 (pi2 (f [b00; b11; e00; e11; dv0]))))))
                                       then pi1 (pi2 (pi2 (f [b00; b11; e00; e11; dv0]))) 
                                       else O |) #? lbl) &
                ((N 1) #? (pi2 (pi2 (pi2 (pi1 (f [b00; b11; e00; e11; dv0])))))) or
                ((N 1) #? (pi2 (pi2 (pi2 (pi1 (pi2 (f [b00; b11; e00; e11; dv0]))))))) or
                (N 1) #? (pi2 (pi2 (pi2 (pi2 (pi2 (f [b00; b11; e00; e11; dv0])))))) else FAlse)]) (z':= [msg b10, msg b01, bol (IF (acc10) & acc01
          then ((((c01) #? (pi1 (pi2 (pi1 (f [b10; b01; e10; e01; dv1]))))) or
                 ((c01) #? (pi1 (pi2 (pi1 (pi2 (f [b10; b01; e10; e01; dv1])))))) or
                 (c01) #? (pi1 (pi2 (pi2 (pi2 (f [b10; b01; e10; e01; dv1])))))) &
                ((| If (c01) #? (pi1 (pi2 (pi2 (pi1 (f [b10; b01; e10; e01; dv1])))))
                       then pi1 (pi1 (f [b10; b01; e10; e01; dv1])) 
                       else If (c01) #? (pi1 (pi2 (pi2 (pi1 (pi2 (f [b10; b01; e10; e01; dv1]))))))
                               then pi1 (pi1 (pi2 (f [b10; b01; e10; e01; dv1]))) 
                               else If (c01) #? (pi1 (pi2 (pi2 (pi2 (pi2 (f [b10; b01; e10; e01; dv1]))))))
                                       then pi1 (pi2 (pi2 (f [b10; b01; e10; e01; dv1]))) 
                                       else O |) #? lbl) &
                ((N 1) #? (pi2 (pi2 (pi2 (pi1 (f [b10; b01; e10; e01; dv1])))))) or
                ((N 1) #? (pi2 (pi2 (pi2 (pi1 (pi2 (f [b10; b01; e10; e01; dv1]))))))) or
                (N 1) #? (pi2 (pi2 (pi2 (pi2 (pi2 (f [b10; b01; e10; e01; dv1]))))))) &
               (((c10) #? (pi1 (pi2 (pi1 (f [b10; b01; e10; e01; dv1]))))) or
                ((c10) #? (pi1 (pi2 (pi1 (pi2 (f [b10; b01; e10; e01; dv1])))))) or
                (c10) #? (pi1 (pi2 (pi2 (pi2 (f [b10; b01; e10; e01; dv1])))))) &
               ((| If (c10) #? (pi1 (pi2 (pi2 (pi1 (f [b10; b01; e10; e01; dv1])))))
                      then pi1 (pi1 (f [b10; b01; e10; e01; dv1])) 
                      else If (c10) #? (pi1 (pi2 (pi2 (pi1 (pi2 (f [b10; b01; e10; e01; dv1]))))))
                              then pi1 (pi1 (pi2 (f [b10; b01; e10; e01; dv1]))) 
                              else If (c10) #? (pi1 (pi2 (pi2 (pi2 (pi2 (f [b10; b01; e10; e01; dv1]))))))
                                      then pi1 (pi2 (pi2 (f [b10; b01; e10; e01; dv1]))) 
                                      else O |) #? lbl) &
               ((N 0) #? (pi2 (pi2 (pi2 (pi1 (f [b10; b01; e10; e01; dv1])))))) or
               ((N 0) #? (pi2 (pi2 (pi2 (pi1 (pi2 (f [b10; b01; e10; e01; dv1]))))))) or
               (N 0) #? (pi2 (pi2 (pi2 (pi2 (pi2 (f [b10; b01; e10; e01; dv1])))))) else FAlse)])
         (f:= (fun z b x => ( ( (pi1 (pi1 (pi1 (pi1 (pi1 (pi1 (tau 1 (pi1 x)))))))),( (pi2 (pi1 (pi1 (pi1 (pi1 (pi1 (tau 1 (pi1 x)))))))), (pi2 (pi1 (tau 1 (pi1 x)))))), (tau 2 (pi1 x), (tau 3 (pi1 x), If (dist (pi2 x))& (pochecks (pi2 x)) & ((isink (pi2 (pi1 (pi2 (pi1 (pi1 (pi1 (pi1 (pi1 (pi1 x))))))))) (pi2 x)) & (isink (pi2 (pi2 (pi2 (pi1 (pi1 (pi1 (pi1 (pi1 (pi1 x))))))))) (pi2 x)) or (! ((isink (pi2 (pi1  (pi2 (pi1 (pi1 (pi1 (pi1 (pi1 (pi1 x))))))))) (pi2 x)) & (isink (pi2 (pi2 (pi2 (pi1 (pi1 (pi1 (pi1 (pi1 (pi1 x))))))))) (pi2 x))))) then (sotrm (pi2 x)) else |_))))) in H8.             
simpl in H8. repeat unfold dist, pochecks, sotrm, p, d, isink, isin in H8.
 rewrite ?proj2 in H8.
 rewrite ?proj1 in H8.
rewrite ?tau1 in H8.
rewrite ?tau2 in H8.
rewrite ?tau3 in H8.
rewrite ?proj2 in H8.
rewrite ?proj1 in H8. rewrite ?proj2 in H8. rewrite ?proj1 in H8. simpl in H8.
restr_swap_in 3 4 H8. simpl in H8.
simpl.

rewrite andB_comm with (b2:= (bnlcheck c01 (N 1) fphi13)). 

 rewrite ?proj2. 
rewrite ?proj1.
rewrite ?tau1.
rewrite ?tau2.
rewrite ?tau3.
rewrite ?proj2.
rewrite ?proj1. simpl. 
assert( (f [b00; b11; e00; e11; dv0]) # fphi03).
reflexivity. rewrite ?H7 in H8.
fold (bnlcheck c00 (N 0) fphi03) in H8.

assert(  (IF (acc00) & acc11
           then ((((c00) #? (pi1 (pi2 (pi1 fphi03)))) or
                  ((c00) #? (pi1 (pi2 (pi1 (pi2 fphi03))))) or (c00) #? (pi1 (pi2 (pi2 (pi2 fphi03))))) &
                 ((| If (c00) #? (pi1 (pi2 (pi2 (pi1 fphi03))))
                        then pi1 (pi1 fphi03) 
                        else If (c00) #? (pi1 (pi2 (pi2 (pi1 (pi2 fphi03)))))
                                then pi1 (pi1 (pi2 fphi03)) 
                                else If (c00) #? (pi1 (pi2 (pi2 (pi2 (pi2 fphi03)))))
                                        then pi1 (pi2 (pi2 fphi03)) 
                                        else O |) #? lbl) &
                 ((N 0) #? (pi2 (pi2 (pi2 (pi1 fphi03))))) or
                 ((N 0) #? (pi2 (pi2 (pi2 (pi1 (pi2 fphi03)))))) or (N 0) #? (pi2 (pi2 (pi2 (pi2 (pi2 fphi03)))))) &
                (((c11) #? (pi1 (pi2 (pi1 fphi03)))) or
                 ((c11) #? (pi1 (pi2 (pi1 (pi2 fphi03))))) or (c11) #? (pi1 (pi2 (pi2 (pi2 fphi03))))) &
                ((| If (c11) #? (pi1 (pi2 (pi2 (pi1 fphi03))))
                       then pi1 (pi1 fphi03) 
                       else If (c11) #? (pi1 (pi2 (pi2 (pi1 (pi2 fphi03)))))
                               then pi1 (pi1 (pi2 fphi03)) 
                               else If (c11) #? (pi1 (pi2 (pi2 (pi2 (pi2 fphi03)))))
                                       then pi1 (pi2 (pi2 fphi03)) 
                                       else O |) #? lbl) &
                ((N 1) #? (pi2 (pi2 (pi2 (pi1 fphi03))))) or
                ((N 1) #? (pi2 (pi2 (pi2 (pi1 (pi2 fphi03)))))) or (N 1) #? (pi2 (pi2 (pi2 (pi2 (pi2 fphi03))))) else FAlse) ## (IF (acc00) & acc11
                                                                                                                                 then (bnlcheck c00 (N 0) fphi03) & (bnlcheck c11 (N 1) fphi03) else FAlse)).

repeat  unfold bnlcheck, bcheck, ncheck, label, isink, isin, dist, pochecks,d, p, sotrm.
 rewrite ?proj2. 
rewrite ?proj1.
rewrite ?tau1.
rewrite ?tau2.
rewrite ?tau3.
rewrite ?proj2.
rewrite ?proj1. simpl.
reflexivity.
rewrite ?H9 in H8.
assert( (label c00 fphi03, (k0, THREE)) # (If (c00) #? (pi1 (pi2 (pi2 (pi1 fphi03))))
                         then pi1 (pi1 fphi03) 
                         else If (c00) #? (pi1 (pi2 (pi2 (pi1 (pi2 fphi03)))))
                                 then pi1 (pi1 (pi2 fphi03)) 
                                 else If (c00) #? (pi1 (pi2 (pi2 (pi2 (pi2 fphi03)))))
                                         then pi1 (pi2 (pi2 fphi03)) 
                                         else O, (k0, THREE))).
repeat unfold label, isin. reflexivity.
rewrite <- ?H10 in H8.
assert ( ( If (c11) #? (pi1 (pi2 (pi2 (pi1 fphi03))))
                         then pi1 (pi1 fphi03) 
                         else If (c11) #? (pi1 (pi2 (pi2 (pi1 (pi2 fphi03)))))
                                 then pi1 (pi1 (pi2 fphi03)) 
                                 else If (c11) #? (pi1 (pi2 (pi2 (pi2 (pi2 fphi03)))))
                                         then pi1 (pi2 (pi2 fphi03)) 
                                         else O, (k1, THREE)) # (label c11 fphi03, (k1, THREE))).
repeat unfold label, isin. reflexivity.
rewrite ?H11 in H8.
clear H7 H9 H10 H11.  

assert( (IF (acc10) & acc01
          then ((((c01) #? (pi1 (pi2 (pi1 (f [b10; b01; e10; e01; dv1]))))) or
                 ((c01) #? (pi1 (pi2 (pi1 (pi2 (f [b10; b01; e10; e01; dv1])))))) or
                 (c01) #? (pi1 (pi2 (pi2 (pi2 (f [b10; b01; e10; e01; dv1])))))) &
                ((| If (c01) #? (pi1 (pi2 (pi2 (pi1 (f [b10; b01; e10; e01; dv1])))))
                       then pi1 (pi1 (f [b10; b01; e10; e01; dv1])) 
                       else If (c01) #? (pi1 (pi2 (pi2 (pi1 (pi2 (f [b10; b01; e10; e01; dv1]))))))
                               then pi1 (pi1 (pi2 (f [b10; b01; e10; e01; dv1]))) 
                               else If (c01) #? (pi1 (pi2 (pi2 (pi2 (pi2 (f [b10; b01; e10; e01; dv1]))))))
                                       then pi1 (pi2 (pi2 (f [b10; b01; e10; e01; dv1]))) 
                                       else O |) #? lbl) &
                ((N 1) #? (pi2 (pi2 (pi2 (pi1 (f [b10; b01; e10; e01; dv1])))))) or
                ((N 1) #? (pi2 (pi2 (pi2 (pi1 (pi2 (f [b10; b01; e10; e01; dv1]))))))) or
                (N 1) #? (pi2 (pi2 (pi2 (pi2 (pi2 (f [b10; b01; e10; e01; dv1]))))))) &
               (((c10) #? (pi1 (pi2 (pi1 (f [b10; b01; e10; e01; dv1]))))) or
                ((c10) #? (pi1 (pi2 (pi1 (pi2 (f [b10; b01; e10; e01; dv1])))))) or
                (c10) #? (pi1 (pi2 (pi2 (pi2 (f [b10; b01; e10; e01; dv1])))))) &
               ((| If (c10) #? (pi1 (pi2 (pi2 (pi1 (f [b10; b01; e10; e01; dv1])))))
                      then pi1 (pi1 (f [b10; b01; e10; e01; dv1])) 
                      else If (c10) #? (pi1 (pi2 (pi2 (pi1 (pi2 (f [b10; b01; e10; e01; dv1]))))))
                              then pi1 (pi1 (pi2 (f [b10; b01; e10; e01; dv1]))) 
                              else If (c10) #? (pi1 (pi2 (pi2 (pi2 (pi2 (f [b10; b01; e10; e01; dv1]))))))
                                      then pi1 (pi2 (pi2 (f [b10; b01; e10; e01; dv1]))) 
                                      else O |) #? lbl) &
               ((N 0) #? (pi2 (pi2 (pi2 (pi1 (f [b10; b01; e10; e01; dv1])))))) or
               ((N 0) #? (pi2 (pi2 (pi2 (pi1 (pi2 (f [b10; b01; e10; e01; dv1]))))))) or
               (N 0) #? (pi2 (pi2 (pi2 (pi2 (pi2 (f [b10; b01; e10; e01; dv1])))))) else FAlse) ## (IF (acc10) & acc01 then (bnlcheck c01 (N 1) fphi13) & (bnlcheck c10 (N 0) fphi13) else FAlse)).  
unfold bnlcheck, bcheck, ncheck, label, isin.  rewrite ?proj1. rewrite ?proj2. rewrite ?tau1; rewrite ?tau2; rewrite ?tau3. reflexivity. rewrite ?H7 in H8.

assert( (If ((c10) #? (pi1 (pi2 (pi2 (pi1 fphi13)))))
                        then pi1 (pi1 fphi13) 
                        else If ((c10) #? (pi1 (pi2 (pi2 (pi1 (pi2 fphi13))))))
                                then pi1 (pi1 (pi2 fphi13)) 
                                else If ((c10) #? (pi1 (pi2 (pi2 (pi2 (pi2 fphi13))))))
                                        then pi1 (pi2 (pi2 fphi13)) 
                                        else O, (k0, THREE)) # (label c10 fphi13, (k0, THREE))).
unfold label, isin. reflexivity.
rewrite ?H9 in H8.
clear H7 H9.  simpl.
assert( (If (c01) #? (pi1 (pi2 (pi2 (pi1 fphi13))))
                        then pi1 (pi1 fphi13) 
                        else If (c01) #? (pi1 (pi2 (pi2 (pi1 (pi2 fphi13)))))
                                then pi1 (pi1 (pi2 fphi13)) 
                                else If (c01) #? (pi1 (pi2 (pi2 (pi2 (pi2 fphi13)))))
                                        then pi1 (pi2 (pi2 fphi13)) 
                                        else O, (k1, THREE)) # (label c01 fphi13, (k1, THREE))).
reflexivity.
rewrite ?H7 in H8.

assert ( ( shufl
                            (pi1
                               (dec
                                  (pi1
                                     (f
                                        [b10; b01; e10; e01; dv1; (enc (label c10 fphi13, (k0, THREE)) (pke 11) (er 9));
                                        (enc (label c01 fphi13, (k1, THREE)) (pke 11) (er 10))])) (ske 11)),
                            pi1
                              (pi2
                                 (dec
                                    (pi1
                                       (f
                                          [b10; b01; e10; e01; dv1; (enc (label c10 fphi13, (k0, THREE)) (pke 11) (er 9));
                                          (enc (label c01 fphi13, (k1, THREE)) (pke 11) (er 10))])) (ske 11))))
                            (pi1
                               (dec
                                  (pi1
                                     (pi2
                                        (f
                                           [b10; b01; e10; e01; dv1; (enc (label c10 fphi13, (k0, THREE)) (pke 11) (er 9));
                                           (enc (label c01 fphi13, (k1, THREE)) (pke 11) (er 10))]))) (ske 11)),
                            pi1
                              (pi2
                                 (dec
                                    (pi1
                                       (pi2
                                          (f
                                             [b10; b01; e10; e01; dv1; (enc (label c10 fphi13, (k0, THREE)) (pke 11) (er 9));
                                             (enc (label c01 fphi13, (k1, THREE)) (pke 11) (er 10))]))) (ske 11))))
                            (pi1
                               (dec
                                  (pi2
                                     (pi2
                                        (f
                                           [b10; b01; e10; e01; dv1; (enc (label c10 fphi13, (k0, THREE)) (pke 11) (er 9));
                                           (enc (label c01 fphi13, (k1, THREE)) (pke 11) (er 10))]))) (ske 11)),
                            pi1
                              (pi2
                                 (dec
                                    (pi2
                                       (pi2
                                          (f
                                             [b10; b01; e10; e01; dv1; (enc (label c10 fphi13, (k0, THREE)) (pke 11) (er 9));
                                             (enc (label c01 fphi13, (k1, THREE)) (pke 11) (er 10))]))) (ske 11)))) ) # (sotrm (f
                          [b10; b01; e10; e01; dv1; (enc (label c10 fphi13, (k0, THREE)) (pke 11) (er 9));
                          (enc (label c01 fphi13, (k1, THREE)) (pke 11) (er 10))]))).
unfold sotrm. unfold p.
unfold d. rewrite ?tau1. unfold tau. rewrite ?proj1. rewrite ?proj2.
reflexivity. rewrite ?H9 in H8. clear H7 H9. simpl.
(** apply freshind to swap k0, k1 on the right side *)
 Axiom aply_fresh_ind: forall n (z z': mylist n), z ~ z'.
 apply aply_fresh_ind.
 (** Goal 2 **)
 simpl. rewrite extIfmr with (b:= (acc00) & acc11).  rewrite extIfmr with (b:= (acc10) & acc01). simpl.
apply IFBRANCH_M1 with (ml1:=  [msg b00, msg b11, bol ((acc00) & acc11) & (bnlcheck c00 (N 0) fphi03) & (bnlcheck c11 (N 1) fphi03)]) (ml2:= [msg b10, msg b01, bol ((acc10) & acc01) & (bnlcheck c10 (N 0) fphi13) & (bnlcheck c01 (N 1) fphi13)]). unfold isink. unfold k0, k1.  repeat rewrite eqm_sym with (m1:= (kc (N 4))).  rewrite infeasible_comp_ck with (n:= 4); auto. unfold orB. 
repeat rewrite IFFALSE_B.
repeat rewrite andB_FAlse_l.  repeat rewrite andB_FAlse_r. repeat rewrite IFFALSE_M. simpl. simpl.  repeat rewrite infeasible_comp_ck with (n:= 4); auto. repeat rewrite IFFALSE_B.   repeat rewrite andB_FAlse_r. repeat rewrite IFFALSE_B.
(** kc (N 3) is equal to one of the decrypted messages of the components **)
Axiom attacker_fwds: forall n r b00 b11 e00 e11 dv0 c00 fphi03 m, (tau 1 (f [b00; b11; e00; e11; dv0; (enc (label c00 fphi03, (kc (N 3), THREE)) (pke n) (er r)); m])) # (enc (label c00 fphi03, (kc (N 3), THREE)) (pke n) (er r)).
unfold d. repeat rewrite attacker_fwds.
(***fix this later ***)

repeat rewrite dep_enc.  rewrite ?proj1, ?proj2. rewrite ?proj1. rewrite eqmeql. unfold notb. repeat rewrite IFTRUE_B.
repeat rewrite andB_FAlse_r. repeat rewrite IFFALSE_M.

(** since the commitment keys are not revealed by the mixer, we could simply apply extcomhid **)
pose proof(compHid_ext). 
pose proof (compHid_ext 3 4 0 1 v0 v1 [] [msg (Mvar 0), msg (Mvar 1)]).
simpl in H9.
unfold Fresh in H9. simpl in H9.
Axiom funcapp: forall n m (z z':mylist n) (f: mylist n -> mylist m), z ~ z' -> (z ++ (f z)) ~ (z' ++ (f z')).
(*
apply funcapp with (f:= (fun z =>
(let c00:= ostomsg (getelt_at_pos 1 z) in
let c11:= ostomsg (getelt_at_pos 2 z) in
let b00:= (bl c00 t r0) in
let b11:= (bl c11 t r1) in
let t2 := ({{ 5 := (bl c00 t r0) }} ({{ 6:=(bl c11 t r1) }} t0)) in
let t3 := ({{ 5 := (bl c00 t r0) }} ({{ 6:=(bl c11 t r1) }} t1)) in
let e00 := (enc ((c00, ((ub c00 t r0 t2), (N 0))), TWO) (pke 11) (er 7)) in
let e11 := (enc ((c11, ((ub c11 t r1 t3), (N 1))), TWO) (pke 11) (er 8)) in
let pv00 := (c00, ((ub c00 t r0 t2), (N 0))) in
let pv11 := (c11, ((ub c11 t r1 t3), (N 1))) in
let fphi02:= (f [b00; b11; e00; e11]) in
let s0 := (If (e00 #? (tau 1 fphi02)) & (e11 #? (tau 2 fphi02)) then (shufl pv00 pv11 (pi1 (d 3 fphi02)))
                            else (If (e00 #? (tau 1 fphi02)) & (e11 #? (tau 3 fphi02)) then (shufl pv00 (pi1 (d 2 fphi02)) pv11)
                                  else (If (e00 #? (tau 2 fphi02)) & (e11 #? (tau 1 fphi02)) then (shufl pv11 pv00  (pi1 (d 3 fphi02)))
                                        else (If (e00 #? (tau 3 fphi02)) & (e11 #? (tau 1 fphi02)) then (shufl pv11  (pi1 (d 2 fphi02)) pv00)
                                              else (If (e00 #? (tau 2 fphi02)) & (e11 #? (tau 3 fphi02)) then (shufl  (pi1 (d 1 fphi02)) pv11 pv00)
                                                    else (If (e00 #? (tau 3 fphi02)) & (e11 #? (tau 2 fphi02)) then (shufl  (pi1 (d 1 fphi02)) pv00 pv11)
                                                          else O)))))) in
let dv0 := (If (dist fphi02) & (pvchecks fphi02) then s0 else |_) in
let fphi03:= (f [b00; b11; e00; e11; dv0]) in
[msg b00, msg b11,
   bol
     ((acc00) & acc11) &
     (bnlcheck c00 (N 0) fphi03) & (bnlcheck c11 (N 1) fphi03),
   bol
     ((acc00) & acc11) &
     (bnlcheck c00 (N 0) fphi03) &
     (IF bnlcheck c11 (N 1) fphi03 then FAlse else TRue),
   msg
     (If (acc00) & acc11
         then (e00, (e11, dv0),
              ((enc (label c00 fphi03, (kc (N 3), THREE)) (pke 11) (er 9)), (O, |_))) 
      else |_)]))) in H9.  simpl in H9. restrproj_in 1 H9. restrproj_in 1 H9.
fold v0 v1 r0 r1 k0 k1 c00 c11 b00 b11 e00 e11 in H9. fold t2 in H9. *)
 (***************)
pose proof(compHid_ext 3 4 0 1 v0 v1 []
(let c00:= (Mvar 0) in
let c11:= (Mvar 1) in
let b00:= (bl c00 t r0) in
let b11:= (bl c11 t r1) in
let t2 := ({{ 5 := (bl c00 t r0) }} ({{ 6:=(bl c11 t r1) }} t0)) in
let t3 := ({{ 5 := (bl c00 t r0) }} ({{ 6:=(bl c11 t r1) }} t1)) in
let e00 := (enc ((c00, ((ub c00 t r0 t2), (N 0))), TWO) (pke 11) (er 7)) in
let e11 := (enc ((c11, ((ub c11 t r1 t3), (N 1))), TWO) (pke 11) (er 8)) in
let pv00 := (c00, ((ub c00 t r0 t2), (N 0))) in
let pv11 := (c11, ((ub c11 t r1 t3), (N 1))) in
let fphi02:= (f [b00; b11; e00; e11]) in
let s0 := (If (e00 #? (tau 1 fphi02)) & (e11 #? (tau 2 fphi02)) then (shufl pv00 pv11 (pi1 (d 3 fphi02)))
                            else (If (e00 #? (tau 1 fphi02)) & (e11 #? (tau 3 fphi02)) then (shufl pv00 (pi1 (d 2 fphi02)) pv11)
                                  else (If (e00 #? (tau 2 fphi02)) & (e11 #? (tau 1 fphi02)) then (shufl pv11 pv00  (pi1 (d 3 fphi02)))
                                        else (If (e00 #? (tau 3 fphi02)) & (e11 #? (tau 1 fphi02)) then (shufl pv11  (pi1 (d 2 fphi02)) pv00)
                                              else (If (e00 #? (tau 2 fphi02)) & (e11 #? (tau 3 fphi02)) then (shufl  (pi1 (d 1 fphi02)) pv11 pv00)
                                                    else (If (e00 #? (tau 3 fphi02)) & (e11 #? (tau 2 fphi02)) then (shufl  (pi1 (d 1 fphi02)) pv00 pv11)
                                                          else O)))))) in
let dv0 := (If (dist fphi02) & (pvchecks fphi02) then s0 else |_) in
let fphi03:= (f [b00; b11; e00; e11; dv0]) in
[msg b00, msg b11,
   bol
     ((acc00) & acc11) &
     (bnlcheck c00 (N 0) fphi03) & (bnlcheck c11 (N 1) fphi03),
   bol
     ((acc00) & acc11) &
     (bnlcheck c00 (N 0) fphi03) &
     (IF bnlcheck c11 (N 1) fphi03 then FAlse else TRue),
   msg
     (If (acc00) & acc11
         then (e00, (e11, dv0),
              ((enc (label c00 fphi03, (kc (N 3), THREE)) (pke 11) (er 9)), (O, |_))) 
      else |_)])).
Axiom aply_ext_comphid: forall n (z z': mylist n), z ~ z'.
apply aply_ext_comphid. Focus 7. apply aply_ext_comphid.
Focus 7. simpl. simpl in H3. simpl in H3. inversion H3. simpl.
 rewrite app_nil_r. reflexivity.
 repeat simpl; reflexivity.