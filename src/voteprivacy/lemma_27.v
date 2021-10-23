
(************************************************************************)
(* Copyright (c) 2017-2018, Ajay Kumar Eeralla <ae266@mail.missouri.edu>*)
(************************************************************************)

Require Export lemma_26.

Set Nested Proofs Allowed.

Import ListNotations.
Axiom ext_blind_enc:  forall {n} (t t0 t1 : message) (z:mylist n), let v0 := (V0 (nonce 0)) in

                                                                     let v1 := (V1 (nonce 0)) in
                                                                                                      (|v0|#?|v1|) ## TRue ->  (Fresh [1; 2; 3; 4] ([msg t, msg v0, msg v1, msg t0, msg t1])  = true) ->  closMylist ([msg t]) = true -> ((Datatypes.length (distMvars [msg t0, msg t1]))=?  2)%nat = true -> bVarMylist [msg t0, msg t1] = nil  ->
    let mvl:= [5; 6] in  (mVarMsg t0) = mvl /\ (mVarMsg t1) = mvl ->
                 let r0 := (r 1) in
                 let r1 := (r 2) in
                 let k0 := (kc (nonce 3)) in
                 let k1 := (kc (nonce 4)) in
                 let c00 := (comm v0 k0) in
                 let c01 := (comm v0 k1) in
                 let c10 := (comm v1 k0) in
                 let c11 := (comm v1 k1) in
                 let t2 := ({{ 5 := (bl c00 t r0) }} ({{ 6:=(bl c11 t r1) }} t0)) in
                 let t3 := ({{ 5 := (bl c00 t r0) }} ({{ 6:=(bl c11 t r1) }} t1)) in
                 let t4 := ({{ 5 := (bl c10 t r0) }} ({{ 6:=(bl c01 t r1) }} t0)) in
                 let t5 := ({{ 5 := (bl c10 t r0) }} ({{ 6:=(bl c01 t r1) }} t1)) in
                 let e00 := (enc ((c00, ((ub c00 t r0 t2), (nonce 0))), TWO) (pke 11) (er 7)) in
                 let e11 := (enc ((c11, ((ub c11 t r1 t3), (nonce 1))), TWO) (pke 11) (er 8)) in
                 let e10 := (enc ((c10, ((ub c10 t r0 t4), (nonce 0))), TWO) (pke 11) (er 7)) in
                 let e01 := (enc ((c01, ((ub c01 t r1 t5), (nonce 1))), TWO) (pke 11) (er 8)) in
                 (occur_name_mylist 100 [msg t, msg t0, msg t1] = false) ->
                 (z++[msg (bl c00 t r0), msg (bl c11 t r1), bol (acc c00 t r0 t2)& (acc c11 t r1 t3),
                        msg (If (acc c00 t r0 t2)& (acc c11 t r1 t3) then (((e00, e11), ((c00, k0), (c11, k1))), ((c00, ((ub c00 t r0 t2), (nonce 0))), (c11, ((ub c11 t r1 t3), (nonce 1))))) else |_ )])
                    ~

                    (z++[msg (bl c10 t r0), msg (bl c01 t r1), bol (acc c10 t r0 t4)& (acc c01 t r1 t5),
                           msg (If (acc c10 t r0 t4)& (acc c01 t r1 t5) then (((e10, e01),((c01, k1), (c10, k0))), ((c01, ((ub c01 t r1 t5), (nonce 1))),(c10, ((ub c10 t r0 t4), (nonce 0))))) else |_)]).

(** This is the lemma14. *)
Lemma lemma_27_opening_phase: forall t t0 t1 : message,
      let v0 := V0 (nonce 0) in
      let v1 := V1 (nonce 0) in
      (| v0 |) #? (| v1 |) ## TRue ->
      Fresh [1; 2; 3; 4] [msg t, msg v0, msg v1, msg t0, msg t1] = true ->
      closMylist [msg t] = true ->
      (Datatypes.length (distMvars [msg t0, msg t1]) =? 2)%nat = true ->
      bVarMylist [msg t0, msg t1] = nil ->
      let mvl := [5; 6] in
      mVarMsg t0 = mvl /\ mVarMsg t1 = mvl ->

                 let r0 := (r 1) in
                 let r1 := (r 2) in
                 let k0 := (kc (nonce 3)) in
                 let k1 := (kc (nonce 4)) in
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
                 let e00 := (enc ((c00, ((ub c00 t r0 t2), (nonce 0))), TWO) (pke 11) (er 7)) in
                 let e11 := (enc ((c11, ((ub c11 t r1 t3), (nonce 1))), TWO) (pke 11) (er 8)) in
                 let e10 := (enc ((c10, ((ub c10 t r0 t4), (nonce 0))), TWO) (pke 11) (er 7)) in
                 let e01 := (enc ((c01, ((ub c01 t r1 t5), (nonce 1))), TWO) (pke 11) (er 8)) in
                 let pv00 := (c00, ((ub c00 t r0 t2), (nonce 0))) in
                 let pv11 := (c11, ((ub c11 t r1 t3), (nonce 1))) in
                 let pv10 := (c10, ((ub c10 t r0 t4), (nonce 0))) in
                 let pv01 := (c01, ((ub c01 t r1 t5), (nonce 1))) in
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
                 let l00 := (If (bnlcheck c00 (nonce 0) fphi03) then (enc ((label c00 fphi03), (k0, THREE)) (pke 11) (er 9)) else O) in
                 let l11 := (If (bnlcheck c11 (nonce 1) fphi03) then (enc ((label c11 fphi03), (k1, THREE)) (pke 11) (er 10)) else O) in
                 let fphi13 := f (toListm phi13) in
                 let l10 := (If (bnlcheck c10 (nonce 0) fphi13) then (enc ((label c10 fphi13), (k0, THREE)) (pke 11) (er 9)) else O) in
                 let l01 := (If (bnlcheck c01 (nonce 1) fphi13) then (enc ((label c01 fphi13), (k1, THREE)) (pke 11) (er 10)) else O) in
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

Proof. Admitted.
