(************************************************************************)
(* Copyright (c) 2015-2019, Ajay Kumar Eeralla                          *)
(*                                                                      *)
(* This work is licensed under the MIT license. The license is          *)
(* described in the file "LICENSE" available at the root of the source  *)
(* or at https://opensource.org/licenses/MIT                            *)
(************************************************************************)

Require Export ex74.

(** This library defines the theorem [EQBRANCH] that states,

[if EQ(x1 , x2) then t[[x1]] else t' = if EQ(x1 ,x2) then t[[x2]] else t'. *)
(** It is a corollary of ex7.4 *)

Theorem eqbrbol_bol :forall ( b1 b2: Bool) (n1 n2 n3 :nat ), (IF (eqb  (Bvar n1)  (Bvar n2)) then [n3 := (Bvar n1)]b1 else b2) ## (IF (eqb  (Bvar n1)(Bvar n2)) then [n3:= (Bvar n2)] b1 else b2).
Proof.
intros.
 assert(H: (IF (eqb  (Bvar n1) (Bvar n2)) then (Bvar n1) else (Bvar n3))  ## (IF (eqb  (Bvar n1) (Bvar n2)) then (Bvar n2) else (Bvar n3))).
apply Example11_B1.
apply Ex12bol_bol with (b:= (eqb (Bvar n1) (Bvar n2)))(n5:= n3)(n6:=n3)(b1:=b1)(b2:=b2) in H.
rewrite invarsub_BBool in H.
apply H.
Qed.

Theorem eqbrbol_msg :forall ( m1 m2: message) (n1 n2 n3 :nat ), ( If (eqb  (Bvar n1)  (Bvar n2)) then ( (n3 := (Bvar n1)) m1) else m2) #  ( If (eqb  (Bvar n1)(Bvar n2)) then ((n3:= (Bvar n2)) m1) else m2).
Proof.
intros.
 assert(H:(IF (eqb (Bvar n1) (Bvar n2)) then (Bvar n1) else (Bvar n3))  ##  (IF (eqb  (Bvar n1) (Bvar n2)) then (Bvar n2) else (Bvar n3))).
apply Example11_B1.
apply Ex12bol_msg with (b:= (eqb (Bvar n1) (Bvar n2)))(n5:= n3)(n6:=n3)(m1:=m1)(m2:=m2) in H.
rewrite invarsub_Bmsg in H.
apply H.
Qed.

Theorem eqbrmsg_msg :forall ( m1 m2 :message) (n1 n2 n3 :nat ), (If (eqm  (Mvar n1)  (Mvar n2)) then {{n3:= (Mvar n1)}}m1 else m2) #   (If (eqm (Mvar n1)(Mvar n2)) then {{n3:= (Mvar n2)}} m1 else m2).
Proof.
intros.
assert(H:   (If (eqm  (Mvar n1) (Mvar n2)) then (Mvar n1) else (Mvar n3) ) # (If (eqm (Mvar n1) (Mvar n2)) then (Mvar n2) else (Mvar n3))).
pose proof(Example11_M1).
apply Example11_M1 with (n1:=n1).
pose proof Ex12msg_msg.
apply Ex12msg_msg  with (b:= (eqm (Mvar n1) (Mvar n2)))(n5:= n3)(n6:=n3)(m1:=m1)(m2:=m2) in H.
rewrite invarsub_mmsg in H.
apply H.
Qed.

Theorem eqbrmsg_bol :forall ( b1 b2: Bool) (n1 n2 n3 :nat ), (IF (eqm  (Mvar n1)  (Mvar n2)) then [[n3 := (Mvar n1)]]b1 else b2) ## (IF (eqm  (Mvar n1)(Mvar n2)) then [[n3:= (Mvar n2)]] b1 else b2).

Proof.
intros.
assert(H:   (If (eqm  (Mvar n1) (Mvar n2)) then (Mvar n1) else (Mvar n3) ) # (If (eqm (Mvar n1) (Mvar n2)) then (Mvar n2) else (Mvar n3))).
pose proof(Example11_M1).
apply Example11_M1 with (n1:=n1).
pose proof Ex12msg_bol.
apply Ex12msg_bol  with (b:= (eqm (Mvar n1) (Mvar n2)))(n5:= n3)(n6:=n3)(b1:=b1)(b2:=b2) in H.
rewrite invarsub_mBool in H.
apply H.
Qed.

Axiom eqbrmsg_msg' :forall (b:Bool) ( m m1 m2 m3 m4 :message) ,  (If (eqm m1 m2) & b then (submsg_msg' m m1 m3) else m4) #  (If (eqm m1 m2) & b then (submsg_msg' m m2 m3) else m4).
Axiom eqbrmsg_msg'' :forall ( m m1 m2:message) (b1 b2: Bool) ,  (IF (eqm m1 m2) then (submsg_bol' m m1 b1) else b2) ##  (IF (eqm m1 m2) then (submsg_bol' m m2 b1) else b2). 
Axiom eqbrmsg_msg''' :forall ( m m1 m2 m3 m4 :message) ,  (If (eqm m1 m2 ) then (submsg_msg' m m1 m3) else m4) #  (If (eqm m1 m2) then (submsg_msg' m m2 m3) else m4).
