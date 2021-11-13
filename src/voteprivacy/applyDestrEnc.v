(************************************************************************) 
(* Copyright (c) 2017-2018, Ajay Kumar Eeralla <ae266@mail.missouri.edu>*)
(************************************************************************)
         
Require Export auxDefs.
  Arguments phi0: simpl never.
Proposition destrEnc:
      let v0 := V0 (f (toListm phi0)) in
      let v1 := V1 (f (toListm phi0)) in
      (vcheck v0) & (vcheck v1) ## TRue ->
      (* Bothsides *)
      let r0 := (r 1) in
      let r1 := (r 2) in
      let k0 := (kc (nonce 3)) in
      let k1 := (kc (nonce 4)) in
      (* Left-side *)
      let c00 := (comm v0 k0) in
      let c11 := (comm v1 k1) in
      let t := pubkey (f (toListm phi0)) in
      let b00 := (bl c00 t r0) in
      let b11 := (bl c11 t r1) in
      let t0 := (((vk 0), (Mvar 5), sign (Mvar 5) (ssk 0) (sr 14)), ((vk 1), (Mvar 6), sign (Mvar 6) (ssk 1) (sr 15))) in
      let t1 := (t0, f (cons t0 nil)) in
      let t2 := ({{ 5 := (bl c00 t r0) }} ({{ 6:=(bl c11 t r1) }} t0)) in
      let t3 := ({{ 5 := (bl c00 t r0) }} ({{ 6:=(bl c11 t r1) }} t1)) in
      let acc00 := (acc c00 t r0 t2) in
      let acc11 := (acc c11 t r1 t3) in
      let e00 := (enc ((c00, ((ub c00 t r0 t2), (nonce 20))), TWO) (pke 11) (er 7)) in
      let e11 := (enc ((c11, ((ub c11 t r1 t3), (nonce 21))), TWO) (pke 11) (er 8)) in
      let phi02:= [msg b00, msg b11, msg e00, msg e11] in
      let fphi02:= f (toListm phi02) in
      let pv00 := (c00, ((ub c00 t r0 t2), (nonce 20))) in
      let pv11 := (c11, ((ub c11 t r1 t3), (nonce 21))) in
      let s0 := (If (! (isin pv00 ((pi1 (d 1 fphi02)), ((pi1 (d 2 fphi02)), (pi1 (d 3 fphi02)))))) then (shufl (pi1 (d 1 fphi02)) (pi1 (d 2 fphi02)) (pi1 (d 3 fphi02))) else O)in
      let dv0 := (If (dist fphi02) & (pvchecks fphi02) then s0 else |_) in
      let t0s0 := (If acc00 & acc11 then (e00, (e11, dv0)) else |_) in

                       (* Right-side *)
      let c10 := (comm v1 k0) in
      let c01 := (comm v0 k1) in 
      let b10 := (bl c10 t r0) in
      let b01 := (bl c01 t r1) in
      let t4 := ({{ 5 := (bl c10 t r0) }} ({{ 6:=(bl c01 t r1) }} t0)) in
      let t5 := ({{ 5 := (bl c10 t r0) }} ({{ 6:=(bl c01 t r1) }} t1)) in
      let acc10 := (acc c10 t r0 t4) in
      let acc01 := (acc c01 t r1 t5) in
      let e10 := (enc ((c10, ((ub c10 t r0 t4), (nonce 20))), TWO) (pke 11) (er 7)) in
      let e01 := (enc ((c01, ((ub c01 t r1 t5), (nonce 21))), TWO) (pke 11) (er 8)) in
      let pv10 := (c10, ((ub c10 t r0 t4), (nonce 20))) in
      let pv01 := (c01, ((ub c01 t r1 t5), (nonce 21))) in
      let phi12:= [msg b10, msg b01, msg e10, msg e01] in
      let fphi12:= f (toListm phi12) in
      let s1 := (If (! (isin pv10 ((pi1 (d 1 fphi12)), ((pi1 (d 2 fphi12)), (pi1 (d 3 fphi12)))))) then (shufl (pi1 (d 1 fphi12)) (pi1 (d 2 fphi12)) (pi1 (d 3 fphi12))) else O)in
      let dv1 := (If (dist fphi12) & (pvchecks fphi12) then s1 else |_) in
      let t1s1 := (If acc10 & acc01 then (e10, (e01, dv1)) else |_) in 
       [msg b00, msg b11, msg t0s0] ~ [msg b10, msg b01, msg t1s1].
Proof. intros.
       aply_cca2Trans (let e00' := (enc ((c00, ((ub c00 t r0 t2), (nonce 100))), TWO) (pke 11) (er 7)) in
                       let phi02':= [msg b00, msg b11, msg e00', msg e11] in
                       let fphi02':= f (toListm phi02') in
                       let s0' := (If (! (isin pv00 ((pi1 (d 1 fphi02')), ((pi1 (d 2 fphi02')), (pi1 (d 3 fphi02')))))) then (shufl (pi1 (d 1 fphi02')) (pi1 (d 2 fphi02')) (pi1 (d 3 fphi02'))) else O)in
                       let dv0' := (If (dist fphi02') & (pvchecks fphi02') then s0' else |_) in
                       let t0s0' := (If acc00 & acc11 then (e00', (e11, dv0')) else |_) in
                       [msg b00, msg b11, msg t0s0'])
                      (let e10' := (enc ((c10, ((ub c10 t r0 t4), (nonce 100))), TWO) (pke 11) (er 7)) in
                  let phi12':= [msg b10, msg b01, msg e10', msg e01] in
      let fphi12':= f (toListm phi12') in
      let s1' := (If (! (isin pv10 ((pi1 (d 1 fphi12')), ((pi1 (d 2 fphi12')), (pi1 (d 3 fphi12')))))) then (shufl (pi1 (d 1 fphi12')) (pi1 (d 2 fphi12')) (pi1 (d 3 fphi12'))) else O)in
      let dv1' := (If (dist fphi12') & (pvchecks fphi12') then s1' else |_) in
      let t1s1' := (If acc10 & acc01 then (e10', (e01, dv1')) else |_) in
      [msg b10, msg b01, msg t1s1']).
 repeat aplyCCA2 150 11 7 7 ((c00, ((ub c00 t r0 t2), (nonce 20))), TWO) ((c00, ((ub c00 t r0 t2), (nonce 100))), TWO).                    
Qed.                  
                     
       
