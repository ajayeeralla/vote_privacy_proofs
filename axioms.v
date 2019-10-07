(************************************************************************)
(* Copyright (c) 2017-2018, Ajay Kumar Eeralla <ae266@mail.missouri.edu>*)     
(************************************************************************)
 
Require Export induction.
(** This library defines equational theory and axioms. The axioms are written for [message] and [Bool] types. *)

(** * Equational theory for DH Protocol *)
Open Scope msg_scope.
Open Scope ind_scope.
Section eqtheory.
Axiom proj1: forall (m1 m2 : message),  (pi1 (m1, m2)) # m1.
Axiom proj2: forall (m1 m2 : message), (pi2 (m1, m2)) # m2.
Axiom len: forall (m:message), | |m| | # |m|.
Axiom eqmeql: forall (m: message), m #? m ## TRue.
End eqtheory.
 
(** * Core Axioms *)
Section core_axioms.

   Section funapp.
Axiom FUNCApp_att4: forall (p1 p2 p3 p4 : nat) {n} (ml1 ml2 : mylist n) {f}, (ml1 ~ ml2 ) -> ([ bol (f (ostomsg (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos  p2 ml1)) (ostomsg (getelt_at_pos  p3 ml1)) (ostomsg (getelt_at_pos  p4 ml1)))] ++ ml1 )
 ~ ([ bol (f (ostomsg (getelt_at_pos  p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)) (ostomsg (getelt_at_pos  p3 ml2)) (ostomsg (getelt_at_pos p4 ml2)))] ++ ml2).

Axiom FUNCApp_mconst: forall  {n} (m:message) (ml1 ml2 : mylist n), (const_msg m = true) -> (ml1 ~ ml2)  -> ([msg m] ++ ml1) ~ ([msg m] ++ ml2).

Axiom FUNCApp_bconst: forall  {n} (b:Bool) (ml1 ml2 : mylist n), (const_bol b = true)-> (ml1 ~ ml2) -> ([bol b] ++ ml1) ~ ([bol b] ++ ml2). 
 
Axiom FUNCApp_f1: forall (p:nat) {n} (ml1 ml2 : mylist n) {f}, (ml1 ~ ml2) -> ([msg (f (ostomsg (getelt_at_pos p ml1)))] ++ ml1) ~
                                                                              ([msg (f (ostomsg (getelt_at_pos p ml2)))] ++ ml2).

Axiom FUNCApp_f2b: forall (p1 p2 :nat) {n} (ml1 ml2 : mylist n) {f}, (ml1 ~ ml2) -> ([bol (f (ostomsg (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos p2 ml1)))] ++ ml1) ~
                                                                                    ([bol (f (ostomsg (getelt_at_pos p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)))] ++ ml2).

Axiom FUNCApp_f2m: forall (p1 p2 :nat) {n} (ml1 ml2 : mylist n) {f}, (ml1 ~ ml2 ) -> ([ msg  (f (ostomsg (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos p2 ml1)))] ++ ml1) ~
                                                                                     ([ msg (f (ostomsg (getelt_at_pos p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)))] ++ ml2).

Axiom FUNCApp_f3b: forall (p1 p2 p3 :nat) {n} (ml1 ml2 : mylist n) {f}, (ml1 ~ ml2 ) -> ([ bol  (f (ostomsg (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos p2 ml1)) (ostomsg (getelt_at_pos p3 ml1)))] ++ ml1) ~
                                                                                        ([ bol  (f (ostomsg (getelt_at_pos p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)) (ostomsg (getelt_at_pos p3 ml2)))] ++ ml2).

Axiom FUNCApp_f3bm: forall (p1 p2 p3 :nat) {n} (ml1 ml2 : mylist n) {f}, (ml1 ~ ml2 ) -> ([ msg  (f (ostobol (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos p2 ml1)) (ostomsg (getelt_at_pos p3 ml1)))] ++ ml1) ~
                                                                                         ([ msg  (f (ostobol (getelt_at_pos p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)) (ostomsg (getelt_at_pos p3 ml2)))] ++ ml2).

Axiom FUNCApp_f3m: forall (p1 p2 p3 :nat) {n} (ml1 ml2 : mylist n) {f}, (ml1 ~ ml2 ) -> ([ msg  (f (ostomsg (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos p2 ml1)) (ostomsg (getelt_at_pos p3 ml1)))] ++ ml1) ~
                                                                                        ([ msg  (f (ostomsg (getelt_at_pos p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)) (ostomsg (getelt_at_pos p3 ml2)))] ++ ml2).

Axiom FUNCApp_f4b: forall (p1 p2 p3 p4 :nat) {n} (ml1 ml2 : mylist n) {f}, (ml1 ~ ml2 ) -> ([ bol  (f (ostomsg (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos p2 ml1)) (ostomsg (getelt_at_pos p3 ml1)) (ostomsg (getelt_at_pos p4 ml1)))] ++ ml1) ~ ( [ bol  (f (ostomsg (getelt_at_pos p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)) (ostomsg (getelt_at_pos p3 ml2)) (ostomsg (getelt_at_pos p4 ml2)))] ++ ml2).

Axiom FUNCApp_f4m: forall (p1 p2 p3 p4 :nat) {n} (ml1 ml2 : mylist n) {f}, (ml1 ~ ml2 ) -> ([ msg  (f (ostomsg (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos p2 ml1)) (ostomsg (getelt_at_pos p3 ml1)) (ostomsg (getelt_at_pos p4 ml1)))] ++ ml1) ~ ([msg (f (ostomsg (getelt_at_pos p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)) (ostomsg (getelt_at_pos p3 ml2)) (ostomsg (getelt_at_pos p4 ml2)))] ++ ml2).

Axiom FUNCApp_f4mb: forall (p1 p2 p3 p4 :nat) {n} (ml1 ml2 : mylist n) {f}, (ml1 ~ ml2 ) -> ([ bol (f (ostomsg (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos p2 ml1)) (ostomsg (getelt_at_pos p3 ml1)) (ostomsg (getelt_at_pos p4 ml1)))] ++ ml1) ~ ([bol (f (ostomsg (getelt_at_pos p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)) (ostomsg (getelt_at_pos p3 ml2)) (ostomsg (getelt_at_pos p4 ml2)))] ++ ml2).

Axiom FUNCApp_g2: forall (p1 p2 :nat) {n} (ml1 ml2 : mylist n) {f}, (ml1 ~ ml2 ) -> ([ bol  (f (ostobol (getelt_at_pos p1 ml1)) (ostobol (getelt_at_pos p2 ml1)))] ++ ml1) ~
                                                                                    ([ bol  (f (ostobol (getelt_at_pos p1 ml2)) (ostobol (getelt_at_pos p2 ml2)))] ++ ml2).

Axiom FUNCApp_g3: forall (p1 p2 p3 :nat) {n} (ml1 ml2 : mylist n){f}, (ml1 ~ ml2 ) -> ([ bol  (f (ostobol (getelt_at_pos p1 ml1)) (ostobol (getelt_at_pos p2 ml1)) (ostobol (getelt_at_pos p3 ml1)))] ++ ml1) ~
                                                                                      ([ bol  (f (ostobol (getelt_at_pos p1 ml2)) (ostobol (getelt_at_pos p2 ml2)) (ostobol (getelt_at_pos p3 ml2)))] ++ ml2).
Axiom FUNCApp_sublist:  forall (m n:nat) {n1} (ml1 ml2:mylist n1){f}, (ml1 ~ ml2) -> ([msg (f  (sublist m n (toListm ml1)))]++ ml1) ~ ([msg (f (sublist m n (toListm ml2)))]++ ml2).

(**************************************************************************************************)

Axiom FUNCApp_const: forall (n m :nat) (ml1 ml2: mylist n) (a: mylist m), (ml1 ~ ml2) -> ((const  a ml1 )++ ml1) ~ ((const a ml2)++ ml2).

Axiom FUNCApp_appelt:  forall (n p :nat) (ml1 ml2: mylist n), (ml1 ~ ml2) -> ([getelt_at_pos  p ml1]  ++ ml1) ~ ([getelt_at_pos  p ml2]++ ml2).

Axiom FUNCApp_eqm: forall (p1 p2:nat) {n} (ml1 ml2: mylist n), (ml1 ~ ml2) -> (([ bol (eqm_at_pos  p1 p2 ml1) ])++ ml1) ~ (([ bol (eqm_at_pos  p1 p2 ml2)])++ ml2).
Axiom FUNCApp_eqb: forall ( p1 p2:nat) {n} (ml1 ml2: mylist n), (ml1 ~ ml2) ->  ( [ bol (eqb_at_pos  p1 p2 ml1)])  ~ ( [ bol (eqb_at_pos  p1 p2 ml2)])  .

Axiom FUNCApp_negpos: forall (p :nat) {n} (ml1 ml2: mylist n), (ml1 ~ ml2) -> ((neg_at_pos p ml1)++ ml1) ~ ((neg_at_pos p ml2)++ ml2).

Axiom FUNCApp_ifmnespair : forall ( p1 p2 p3 p4 : nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2) -> ([msg (ifm_nespair  p1 p2 p3 p4 ml1)]++ ml1) ~([msg (ifm_nespair  p1 p2 p3 p4 ml2)]++ ml2).

Axiom FUNCApp_ifmpair: forall ( p1 p2 p3 p4  : nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2) -> ([msg (ifm_pair  p1 p2 p3 p4 ml1)]++ ml1) ~ ([ msg (ifm_pair p1 p2 p3 p4 ml2)]++ ml2). 
(*
Axiom FUNCApp_expatpos: forall (p1 p2 p3 : nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2) -> ( [msg (exp_at_pos  p1 p2 p3  ml1)]++ ml1) ~ ( [msg (exp_at_pos  p1 p2 p3  ml2)]) .

Axiom FUNCApp_att : forall {n} (ml1 ml2: mylist n) (l1 l2 :list message ), (ml1 ~ ml2) -> ([msg (f l1)] ++ ml1++ ml1) ~ ([msg (f l2)] ++ ml2++ ml2).

Axiom FUNCApp_reveal:  forall ( p:nat) {n} (ml1 ml2 : mylist n) , (ml1 ~ ml2) -> ([msg (reveal_at_pos p ml1)] ++ml1   ++ ml1) ~ ([msg (reveal_at_pos p ml2)] ++ml2 ++ ml2).
*)
Axiom FUNCApp_to:  forall (p:nat) {n} (ml1 ml2 : mylist n) , (ml1 ~ ml2) -> ([msg (to_at_pos p ml1)] ++ ml1)  ~ ([msg (to_at_pos p ml2)] ++ ml2).
(*
Axiom FUNCApp_act:  forall (p:nat) {n} (ml1 ml2 : mylist n) , (ml1 ~ ml2) -> ([msg (act_at_pos p ml1)] ++ ml1)  ~ ([msg (act_at_pos p ml2)] ++ ml2++ ml2).

Axiom FUNCApp_new : forall {n} (ml1 ml2 : mylist n) , (ml1 ~ ml2) -> ([msg new ] ++ ml1++ ml1) ~ ([msg new ] ++ ml2++ ml2).
*)
Axiom FUNCApp_O : forall {n} (ml1 ml2 : mylist n) , (ml1 ~ ml2) -> ( [msg O]++ ml1) ~ ([msg O]++ ml2).
(*
Axiom FUNCApp_acc : forall {n} (ml1 ml2 : mylist n) , (ml1 ~ ml2) -> ( [msg acc]++ ml1) ~ ([msg acc]++ ml2).

Axiom FUNCApp_session : forall ( m: nat ) {n} (ml1 ml2 : mylist m) , (ml1 ~ ml2) -> ([msg (i n) ] ++ ml1++ ml1) ~ ([msg (i n) ] ++ ml2++ ml2).
*)
Axiom FUNCApp_andB : forall (p1 p2 :nat) {m} (ml1 ml2 : mylist m), (ml1 ~ ml2) -> ([bol (andB_at_pos p1 p2 ml1)]++ ml1) ~  ([bol (andB_at_pos p1 p2 ml2)]++ ml2).

Axiom FUNCApp_notB : forall (p :nat) {m} (ml1 ml2:mylist m), (ml1 ~ ml2) -> ([bol (notB_at_pos  p ml1)]++ ml1) ~ ([bol (notB_at_pos p ml2)]++ ml2).
(*
Axiom FUNCApp_m : forall (p :nat) {m} (ml1 ml2:mylist m), (ml1 ~ ml2) -> ( [ msg (m_at_pos  p ml1)] ++ ml1++ ml1) ~  (  [msg (m_at_pos  p ml2) ] ++ ml2++ ml2).

Axiom FUNCApp_elt :   forall (p   :nat) {m} (ml1 ml2:mylist m), (ml1~ml2) ->  ([getelt_at_pos  p ml1 ] ++ ml1) ~ ([  getelt_at_pos p ml2]++ ml2).
*)
Axiom FUNCApp_pair: forall (p1 p2 :nat) {m} (ml1 ml2 : mylist m), (ml1 ~ ml2) -> ([msg ( ostomsg (getelt_at_pos p1 ml1) , ostomsg ( getelt_at_pos p2 ml1 )) ]++ ml1) ~ ([ msg ( ostomsg (getelt_at_pos p1 ml2) , ostomsg ( getelt_at_pos p2 ml2 ))] ++ ml2).
 

Axiom FUNCApp_pi1: forall (p :nat)  {m} (ml1 ml2 : mylist m), (ml1 ~ ml2) -> ( [ msg (pi1 (ostomsg (getelt_at_pos p ml1)))] ++ ml1) ~  ( [ msg (pi1 (ostomsg (getelt_at_pos p ml2)))] ++ ml2).

Axiom FUNCApp_pi2: forall (p :nat)  {m} (ml1 ml2 : mylist m), (ml1 ~ ml2) -> ( [ msg (pi2 (ostomsg (getelt_at_pos p ml1)))] ++ ml1 ) ~  ( [ msg (pi2 (ostomsg (getelt_at_pos p ml2)))] ++ ml2).
End funapp.
   
(** [RESTR] *)
Section restr.
(** Indistinguishability is closed under projections *)
Local Open Scope ind_scope.
Axiom RESTR_proj : forall ( p :nat) {m} (ml1 ml2 :mylist m), ml1 ~ ml2 -> (proj_at_pos p ml1) ~ (proj_at_pos p ml2).

Axiom RESTR_dropls: forall {n} (ml1 ml2: mylist n), ml1 ~ ml2 -> (droplastsec ml1) ~ (droplastsec ml2).

Axiom RESTR_dropone: forall {n} (ml1 ml2: mylist n), ml1 ~ ml2 -> (dropone ml1) ~ (dropone ml2).

(** Indistinguishability is closed under permutations *)

Axiom RESTR_swap : forall (p1 p2 : nat) {n} (ml1 ml2 : mylist n), ml1~ ml2 -> (swap_mylist p1 p2 ml1) ~ (swap_mylist p1 p2 ml2).

Axiom RESTR_swapls: forall {n1 n2} (ml1 ml2 : mylist n1) (ml3 ml4 :mylist n2) , (ml1 ++ ml3) ~ (ml2 ++ ml4) -> (ml3 ++ ml1) ~ (ml4 ++ ml2).

End restr.

(** Axioms for indistinguishability *)

Axiom REFL: forall {n} (x : mylist n), x ~ x.
Axiom SYM: forall {n} (x y : mylist n), x ~ y -> y ~ x.
Axiom TRANS: forall {n} (x y z : mylist n), x ~ y /\ y ~ z -> x ~ z.
Axiom RESTR: forall {n m} (x y : mylist n) (p: mylist n -> mylist m), x ~ y -> (p x) ~ (p y). 
Axiom FUNCAPP: forall {n m} (x y : mylist n) (f: mylist n -> mylist m), x ~ y -> (x ++ (f x)) ~ (y ++ (f y)).
Axiom IFDIST: not([bol TRue] ~ [bol FAlse]).

(** Axioms for equality *)
Axiom EQCONG_M: forall (x y : message) {f}, x # y -> (f x) # (f y).
Axiom EQCONG_B: forall (x y : Bool) {f}, x ## y -> (f x) ## (f y).

(** Axioms for [if_then_else] symbol. *)

(** [IFSAME] *)

Axiom IFSAME_M: forall (b:Bool) (x : message), (If b then x else x) # x.

Axiom IFSAME_B: forall (b:Bool) (b1 : Bool),  (IF b then b1 else b1) ## b1.

(** [IFEVAL] *)

Axiom IFEVAL_B : forall (b1 b2 : Bool)(n:nat), (IF (Bvar n) then b1 else b2) ## (IF (Bvar n) then ([n := TRue] b1) else ([n := FAlse] b2)).

Axiom IFEVAL_M : forall (t1 t2 : message) (n:nat), (If (Bvar n) then t1 else t2) # (If (Bvar n) then ((n := TRue) t1) else ((n := FAlse) t2)).

Axiom IFEVAL_B' : forall (b b1 b2 : Bool), (IF b then b1 else b2) ## (IF b then (subbol_bol' b TRue b1) else (subbol_bol' b FAlse b2)).

Axiom IFEVAL_M' : forall (b:Bool)(t1 t2 : message), (If b then t1 else t2) #(If b then (subbol_msg' b TRue t1) else (subbol_msg' b FAlse t2)).

(** [IFTRue] *)

Axiom IFTRUE_M : forall (x y : message),  (If TRue then x else y) # x .

Axiom IFTRUE_B : forall (b1 b2 : Bool), (IF TRue then b1 else b2) ## b1.

(** [IFFAlse] *)

Axiom IFFALSE_M: forall (x y : message), (If FAlse then x else y) # y.

Axiom IFFALSE_B: forall (b1 b2 : Bool), (IF FAlse then b1 else b2) ## b2.

(** [IFBRANCH *)


Axiom  IFBRANCH_M1: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(x x' y y':message), (ml1 ++ [ bol b , msg x] ) ~  ( ml2 ++ [ bol b', msg x'])  ->  (ml1 ++ [bol b , msg y ] ) ~( ml2 ++ [bol b' , msg y']) -> (ml1 ++  [ msg (If b then x else y)])~ ( ml2 ++ [ msg (If b' then x' else y')]).

Axiom IFBRANCH_M2: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(x1 x1' x2 x2' y1 y1' y2 y2' :message), (ml1 ++ [ bol b , msg x1, msg x2] ) ~  ( ml2 ++ [ bol b', msg x1' , msg x2'])  ->  (ml1 ++ [bol b, msg y1, msg y2 ] ) ~( ml2 ++ [bol b', msg y1', msg y2']) 
                                                                                     -> (ml1 ++  [ msg (If b then x1 else y1) , msg (If b then x2 else y2) ])~ ( ml2 ++ [ msg (If b' then x1' else y1') , msg (If b' then x2' else y2')]).

(** [Fresh] *)

Definition r (n:nat) := (re (N n)).
Notation " '[[' x ']]'" := (cons x nil): msg_scope.

Axiom FRESHIND : forall (n n1 n2:nat) (v w: mylist n),   (v ~ w) ->   ((closMylist (v++w)) = true) /\ ( (Fresh [[n1]] (v++w)) = true) /\ ( (Fresh [[n2]] (v++w)) = true) -> ((msg  (N n1)) +++ v) ~ (( msg  (N n2)) +++w ).

Axiom FRESHNEQ: forall (n : nat) (m : message), ((closMsg m) = true)/\ ( (Fresh [[n]] [msg m]) = true) ->[bol (eqm (N n) m)]~ [bol FAlse]. 


Axiom FRESHIND_rs: forall (n n1 n2:nat) (v w: mylist n),  (v ~ w) -> ((closMylist (v++w)) = true) /\ ( (Fresh [[n1]]  (v++w)) = true) /\ ( (Fresh [[n2]] (v++w)) = true)   -> ((msg (r n1) ) +++ v) ~ (( msg (r n2)) +++w ).


Section ifbranch.
(** [IFBRANCH] *)
(*
Axiom IFBRANCH_M: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(x x' y y':message), (ml1 ++ [ bol b ; msg x] ) ~  ( ml2 ++ [ bol b'; msg x'])  ->  (ml1 ++ [bol b ; msg y ] ) ~( ml2 ++ [bol b' ; msg y'])
-> (ml1 ++ [bol b ;msg (ifm b x y)])~ ( ml2 ++ [bol b' ; msg (ifm b' x' y')]).

Axiom IFBRANCH_B: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(b1 b1' b2 b2':Bool), (ml1 ++ [bol b ;bol b1]) ~ ( ml2 ++ [bol b' ; bol b1'])  ->  (ml1 ++ [ bol b; bol b2]) ~( ml2 ++ [bol b'; bol b2'])
-> (ml1 ++ [ bol b ;bol (ifb b b1 b2)])~ (  ml2 ++ [bol b' ; bol (ifb b' b1' b2')] ).
 *)


Axiom IFBRANCH_M3: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(x1 x1' x2 x2' x3 x3' y1 y1' y2 y2' y3 y3' :message), (ml1 ++ [ bol b , msg x1, msg x2 , msg x3] ) ~  ( ml2 ++ [ bol b', msg x1' , msg x2' , msg x3'])  ->  (ml1 ++ [bol b , msg y1 , msg y2 , msg y3 ] ) ~( ml2 ++ [bol b' , msg y1', msg y2' , msg y3'])                                                                                               -> (ml1 ++  [ msg (ifm_then_else_ b x1 y1) , msg (ifm_then_else_ b x2 y2) , msg (ifm_then_else_ b x3 y3) ])~ ( ml2 ++ [ msg (ifm_then_else_ b' x1' y1') , msg (ifm_then_else_ b' x2' y2') , msg (ifm_then_else_ b' x3' y3')]).

Axiom IFBRANCH_M4: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(x1 x1' x2 x2' x3 x3' x4 x4' y1 y1' y2 y2' y3 y3' y4 y4' :message), (ml1 ++ [ bol b , msg x1, msg x2 , msg x3, msg x4] ) ~  ( ml2 ++ [ bol b', msg x1' , msg x2' , msg x3', msg x4'])  ->  (ml1 ++ [bol b , msg y1 , msg y2 , msg y3, msg y4 ] ) ~( ml2 ++ [bol b' , msg y1', msg y2' , msg y3', msg y4'])  -> (ml1 ++  [ msg (ifm_then_else_ b x1 y1) , msg (ifm_then_else_ b x2 y2) , msg (ifm_then_else_ b x3 y3) , msg (ifm_then_else_ b x4 y4) ])~ ( ml2 ++ [ msg (ifm_then_else_ b' x1' y1') , msg (ifm_then_else_ b' x2' y2') , msg (ifm_then_else_ b' x3' y3') ,  msg (ifm_then_else_ b' x4' y4')]).

Axiom IFBRANCH_M5: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(x1 x1' x2 x2' x3 x3' x4 x4' x5 x5' y1 y1' y2 y2' y3 y3' y4 y4' y5 y5' :message), (ml1 ++ [ bol b , msg x1, msg x2 , msg x3, msg x4 , msg x5] ) ~  ( ml2 ++ [ bol b', msg x1' , msg x2' , msg x3', msg x4', msg x5'])  ->  (ml1 ++ [bol b , msg y1 , msg y2 , msg y3, msg y4, msg y5 ] ) ~( ml2 ++ [bol b' , msg y1', msg y2' , msg y3', msg y4', msg y5'])  -> (ml1 ++  [ msg (ifm_then_else_ b x1 y1) , msg (ifm_then_else_ b x2 y2) , msg (ifm_then_else_ b x3 y3) , msg (ifm_then_else_ b x4 y4), msg (ifm_then_else_ b x5 y5) ])~ ( ml2 ++ [ msg (ifm_then_else_ b' x1' y1') , msg (ifm_then_else_ b' x2' y2') , msg (ifm_then_else_ b' x3' y3') ,  msg (ifm_then_else_ b' x4' y4'), msg (ifm_then_else_ b' x5' y5')]).

Axiom IFBRANCH_M6: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(x1 x1' x2 x2' x3 x3' x4 x4' x5 x5' x6 x6' y1 y1' y2 y2' y3 y3' y4 y4' y5 y5' y6 y6':message), (ml1 ++ [ bol b , msg x1, msg x2 , msg x3, msg x4 , msg x5, msg x6] ) ~  ( ml2 ++ [ bol b', msg x1' , msg x2' , msg x3', msg x4', msg x5' , msg x6'])  ->  (ml1 ++ [bol b , msg y1 , msg y2 , msg y3, msg y4, msg y5, msg y6] ) ~( ml2 ++ [bol b' , msg y1', msg y2' , msg y3', msg y4', msg y5', msg y6'])  -> (ml1 ++  [ msg (ifm_then_else_ b x1 y1) , msg (ifm_then_else_ b x2 y2) , msg (ifm_then_else_ b x3 y3) , msg (ifm_then_else_ b x4 y4), msg (ifm_then_else_ b x5 y5), msg (ifm_then_else_ b x6 y6)])~ ( ml2 ++ [ msg (ifm_then_else_ b' x1' y1') , msg (ifm_then_else_ b' x2' y2') , msg (ifm_then_else_ b' x3' y3') ,  msg (ifm_then_else_ b' x4' y4'), msg (ifm_then_else_ b' x5' y5'), msg (ifm_then_else_ b' x6' y6')]). 

Axiom IFBRANCH_M7: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(x1 x1' x2 x2' x3 x3' x4 x4' x5 x5' x6 x6' x7 x7' y1 y1' y2 y2' y3 y3' y4 y4' y5 y5' y6 y6' y7 y7' :message), (ml1 ++ [ bol b , msg x1, msg x2 , msg x3, msg x4 , msg x5, msg x6 , msg x7] ) ~  ( ml2 ++ [ bol b', msg x1' , msg x2' , msg x3', msg x4', msg x5' , msg x6' , msg x7'])  ->  (ml1 ++ [bol b , msg y1 , msg y2 , msg y3, msg y4, msg y5, msg y6 , msg y7 ] ) ~( ml2 ++ [bol b' , msg y1', msg y2' , msg y3', msg y4', msg y5', msg y6' , msg y7'])  -> (ml1 ++  [ msg (ifm_then_else_ b x1 y1) , msg (ifm_then_else_ b x2 y2) , msg (ifm_then_else_ b x3 y3) , msg (ifm_then_else_ b x4 y4), msg (ifm_then_else_ b x5 y5), msg (ifm_then_else_ b x6 y6), msg (ifm_then_else_ b x7 y7) ])~ ( ml2 ++ [ msg (ifm_then_else_ b' x1' y1') , msg (ifm_then_else_ b' x2' y2') , msg (ifm_then_else_ b' x3' y3') ,  msg (ifm_then_else_ b' x4' y4'), msg (ifm_then_else_ b' x5' y5'), msg (ifm_then_else_ b' x6' y6'), msg (ifm_then_else_ b' x7' y7')]).

 
Axiom IFBRANCH_M8: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(x1 x1' x2 x2' x3 x3' x4 x4' x5 x5' x6 x6' x7 x7' x8 x8' y1 y1' y2 y2' y3 y3' y4 y4' y5 y5' y6 y6' y7 y7' y8 y8' :message), (ml1 ++ [ bol b , msg x1, msg x2 , msg x3, msg x4 , msg x5, msg x6 , msg x7, msg x8] ) ~  ( ml2 ++ [ bol b', msg x1' , msg x2' , msg x3', msg x4', msg x5' , msg x6' , msg x7', msg x8'])  ->  (ml1 ++ [bol b , msg y1 , msg y2 , msg y3, msg y4, msg y5, msg y6 , msg y7, msg y8 ] ) ~( ml2 ++ [bol b' , msg y1', msg y2' , msg y3', msg y4', msg y5', msg y6' , msg y7', msg y8'])  -> (ml1 ++  [ msg (ifm_then_else_ b x1 y1) , msg (ifm_then_else_ b x2 y2) , msg (ifm_then_else_ b x3 y3) , msg (ifm_then_else_ b x4 y4), msg (ifm_then_else_ b x5 y5), msg (ifm_then_else_ b x6 y6), msg (ifm_then_else_ b x7 y7), msg (ifm_then_else_ b x8 y8) ])~ ( ml2 ++ [ msg (ifm_then_else_ b' x1' y1') , msg (ifm_then_else_ b' x2' y2') , msg (ifm_then_else_ b' x3' y3') ,  msg (ifm_then_else_ b' x4' y4'), msg (ifm_then_else_ b' x5' y5'), msg (ifm_then_else_ b' x6' y6'), msg (ifm_then_else_ b' x7' y7'), msg (ifm_then_else_ b' x8' y8')]).
 
Axiom IFBRANCH_M9: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(x1 x1' x2 x2' x3 x3' x4 x4' x5 x5' x6 x6' x7 x7' x8 x8' x9 x9' y1 y1' y2 y2' y3 y3' y4 y4' y5 y5' y6 y6' y7 y7' y8 y8' y9 y9' :message), (ml1 ++ [ bol b , msg x1, msg x2 , msg x3, msg x4 , msg x5, msg x6 , msg x7, msg x8, msg x9] ) ~  ( ml2 ++ [ bol b', msg x1' , msg x2' , msg x3', msg x4', msg x5' , msg x6' , msg x7', msg x8', msg x9'])  ->  (ml1 ++ [bol b , msg y1 , msg y2 , msg y3, msg y4, msg y5, msg y6 , msg y7, msg y8, msg y9 ] ) ~( ml2 ++ [bol b' , msg y1', msg y2' , msg y3', msg y4', msg y5', msg y6' , msg y7', msg y8', msg y9'])  -> (ml1 ++  [ msg (ifm_then_else_ b x1 y1) , msg (ifm_then_else_ b x2 y2) , msg (ifm_then_else_ b x3 y3) , msg (ifm_then_else_ b x4 y4), msg (ifm_then_else_ b x5 y5), msg (ifm_then_else_ b x6 y6), msg (ifm_then_else_ b x7 y7), msg (ifm_then_else_ b x8 y8), msg (ifm_then_else_ b x9 y9) ])~ ( ml2 ++ [ msg (ifm_then_else_ b' x1' y1') , msg (ifm_then_else_ b' x2' y2') , msg (ifm_then_else_ b' x3' y3') ,  msg (ifm_then_else_ b' x4' y4'), msg (ifm_then_else_ b' x5' y5'), msg (ifm_then_else_ b' x6' y6'), msg (ifm_then_else_ b' x7' y7'), msg (ifm_then_else_ b' x8' y8'), msg (ifm_then_else_ b' x9' y9')]).

Axiom IFBRANCH_M10: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(x1 x1' x2 x2' x3 x3' x4 x4' x5 x5' x6 x6' x7 x7' x8 x8' x9 x9' x10 x10' y1 y1' y2 y2' y3 y3' y4 y4' y5 y5' y6 y6' y7 y7' y8 y8' y9 y9' y10 y10' :message), (ml1 ++ [ bol b , msg x1, msg x2 , msg x3, msg x4 , msg x5, msg x6 , msg x7, msg x8, msg x9, msg x10] ) ~  ( ml2 ++ [ bol b', msg x1' , msg x2' , msg x3', msg x4', msg x5' , msg x6' , msg x7', msg x8', msg x9', msg x10'])  ->  (ml1 ++ [bol b , msg y1 , msg y2 , msg y3, msg y4, msg y5, msg y6 , msg y7, msg y8, msg y9, msg y10 ] ) ~( ml2 ++ [bol b' , msg y1', msg y2' , msg y3', msg y4', msg y5', msg y6' , msg y7', msg y8', msg y9', msg y10'])  -> (ml1 ++  [ msg (ifm_then_else_ b x1 y1) , msg (ifm_then_else_ b x2 y2) , msg (ifm_then_else_ b x3 y3) , msg (ifm_then_else_ b x4 y4), msg (ifm_then_else_ b x5 y5), msg (ifm_then_else_ b x6 y6), msg (ifm_then_else_ b x7 y7), msg (ifm_then_else_ b x8 y8), msg (ifm_then_else_ b x9 y9), msg (ifm_then_else_ b x10 y10) ])~ ( ml2 ++ [ msg (ifm_then_else_ b' x1' y1') , msg (ifm_then_else_ b' x2' y2') , msg (ifm_then_else_ b' x3' y3') ,  msg (ifm_then_else_ b' x4' y4'), msg (ifm_then_else_ b' x5' y5'), msg (ifm_then_else_ b' x6' y6'), msg (ifm_then_else_ b' x7' y7'), msg (ifm_then_else_ b' x8' y8'), msg (ifm_then_else_ b' x9' y9'), msg (ifm_then_else_ b' x10' y10')]).

End ifbranch.
End core_axioms.

(** * Auxilary Axioms *)
Section aux_thms.

(** Equality ([Bool] or [message]) is closed under substitution. *)

Theorem Forall_ELM_EVAL_M: forall (x:Bool) (n:nat) (t1 t2 :message), ( t1 # t2 ) ->  ((( n:=x )t1) # ((n:=x)t2)).
Proof. intros; rewriteHyp;try reflexivity. Qed.

  Theorem Forall_ELM_EVAL_B: forall (b:Bool) (n:nat) (b1 b2 :Bool), (  b1 ## b2 ) ->  ( ([n:=b] b1) ## ([n:=b] b2)).
Proof. intros; rewriteHyp;try reflexivity. Qed.
Theorem Forall_ELM_EVAL_M1: forall (x:message) (n:nat) (t1 t2 :message), (t1 # t2 ) ->  ({{n:=x}} t1 # {{n:=x}}t2).
  Proof. intros; rewriteHyp;try reflexivity. Qed.
Theorem Forall_ELM_EVAL_B1: forall (b:message) (n:nat) (b1 b2 :Bool), ( b1 ## b2 ) ->  ( [[n:=b]] b1 ## [[n:=b]] b2).
Proof. intros; rewriteHyp;try reflexivity. Qed.
Theorem Forall_ELM_EVAL_M2: forall (x:Bool) (n:nat) (t1 t2 :message), (t1 # t2)  ->  ( (( n:=x )t1) # ((n:=x)t2 )).
  Proof. intros; rewriteHyp;try reflexivity. Qed.
Theorem Forall_ELM_EVAL_B2: forall (b:Bool) (n:nat) (b1 b2 :Bool), (b1 ## b2)  ->   ( [n:=b] b1 ## [n:=b] b2).
Proof. intros; rewriteHyp;try reflexivity. Qed.
Theorem Forall_ELM_EVAL_M3: forall (x:message) (n:nat) (t1 t2 :message),  ( t1 # t2)  ->  ( {{n:=x}} t1  # {{n:=x}}t2).
  Proof. intros; rewriteHyp;try reflexivity. Qed.
  Theorem Forall_ELM_EVAL_B3: forall (b:message) (n:nat) (b1 b2 :Bool), ( b1 ## b2) ->   ( [[n:=b]] b1 ## [[n:=b]] b2).
    Proof. intros; rewriteHyp;try reflexivity. Qed.
End aux_thms.

(*
(***substitutions under attacker functions**********)
Axiom sub_msg_f : forall ( n :nat) (s:message) {m} (l: ilist message m), {{ n := s }} (f l) # (f (submsg_mlist n s l)).
Axiom sub_bol_f : forall ( n :nat) (b: Bool) {m} (l: ilist message m), ( n := b ) (f l) # (f (subbol_mlist n b l)).
 *)

(** There always exists a natural number which doesn't occur in lists of terms. *)

Fixpoint occurNlist (n:nat) (nl: Nlist):bool :=
  match nl with
  | [ ] => false
  | h :: t => beq_nat n h || occurNlist n t
  end.

Axiom existsnMylist: forall (m :nat) (nl : Nlist)(bl:mylist m), exists n , (occurNlist n nl = false) /\ (occur_name_mylist n bl = false).
Axiom existsnBlist : forall (m:nat) (nl : Nlist)(bl:Blist ), exists n , (occurNlist n nl = false) /\ (occurBlist n bl = false).
Axiom existsnMlist: forall (m :nat) (nl : Nlist)(ml:Mlist), exists n , (occurNlist n nl = false) /\ (occurMlist n ml = false).
(*
Axiom subconct: forall (n1 n2 n:nat) (ml1 : mylist n1)(ml2 : mylist n2)(b:Bool), ((subbol_mylist n b (ml1 ++ ml2)) =(subbol_mylist n b ml1 ++ subbol_mylist n b ml2)).
Axiom subinmsg : forall (n : nat)(b:Bool) (t1:message), ( (subbol_os n b (msg t1) ) = (msg ((n := b) t1))).
Axiom subinbol : forall (n : nat)(b:Bool) (t1:Bool), ( (subbol_os n b (bol t1) ) = (bol ([n := b] t1))).
*)

(** Substitution inside substitution. *)

Axiom notocc_bolmm: forall (n1 n2 : nat) (b: Bool) (m1 m2 : message), (occur_name_msg n1 m2) = false -> ( n1 :=  b) ({{ n2:= m1}}  m2) = ({{ n2 := (( n1 := b) m1) }} m2).
(*Axiom occ_bolmm: forall (n1 n2 : nat) (b: Bool) (m1 m2 : message), (notoccur_name_msg n1 m2) = false -> ( n1 :=  b)  ((submsg_msg n2 m1)  m2) = (submsg_msg n2 (( n1 := b) m1)) (( n1 := b)m2) .*)

Axiom notocc_bolbb : forall  (n1 n2 :nat) (b b1 b2:Bool), (occur_name_bol n1 b2) = false -> ([ n1 :=  b]  [ n2 := b1]  b2)  =    ( [ n2 := ([n1:=b] b1)]  b2) .
(*Axiom occ_bolbb : forall  (n1 n2 :nat) (b b1 b2:Bool), (notoccur_bol n1 b2) = false -> ([ n1 :=  b]  [ n2 := b1]  b2)  =    ( [ n2 := ([n1:=b] b1)]  ([n1:=b] b2)) .*)

Axiom notocc_bolmb : forall (n1 n2 :nat) (b  b1:Bool) (m:message),(occur_name_bol n1 b1) = false -> ([ n1 :=  b]  [[ n2 := m]]  b1)  =    ( [[ n2 := ((n1 := b) m)]]  b1).
(*Axiom occ_bolmb : forall (n1 n2 :nat) (b  b1:Bool) (m:message),(notoccur_bol n1 b1) = false -> ([ n1 :=  b]  [[ n2 := m]]  b1)  =    ( [[ n2 := ((n1 := b) m)]]  ([ n1 :=  b] b1)).*)

Axiom notocc_bolbm : forall (n1 n2 :nat) (b  b1:Bool) (m:message),(occur_name_msg n1 m) = false -> ( ( n1 :=  b)  (( n2 := b1) m)  =    ( ( n2 := ([n1 := b] b1))  m)).
(*Axiom occ_bolbm : forall (n1 n2 :nat) (b  b1:Bool) (m:message),(notoccur_msg n1 m) = false -> ( ( n1 :=  b)  (( n2 := b1) m)  =    ( ( n2 := ([n1 := b] b1))  (n1 := b)m)).*)


(********************************************************************************) 
Axiom notoccn_Bool: forall (n:nat)(b t:Bool), ((occur_name_bol n t) = true )-> ([n := b]t =  t).
Axiom notoccn_msg: forall (n:nat)(b:Bool)(t:message), ((occur_name_msg n t) = true) -> ((n:= b)t) = t.
(***********************************************************************************)
 
(** Trivially sound axioms. *)

Axiom invarsub_Bmsg : forall(n:nat)(t:message), ((n:= (Bvar n))t = t).
Axiom invarsub_BBool: forall(n:nat)(b:Bool), ([n:=(Bvar n)] b) = b.
Axiom invarsub_mBool : forall(n:nat)(b: Bool), ([[n:= (Mvar n)]] b) = b. 
Axiom invarsub_mmsg : forall(n:nat)(t: message),{{n:= (Mvar n)}} t = t.

(*
(**Axiom RESTR_Perm: forall(n1 n2 n3 n4 n5:nat) (nl1 ml1 : mylist n1)(nl2 ml2 : mylist n2)(nl3 ml3 : mylist n3)(ml4 nl4 : mylist n4) (ml5 nl5 : mylist n5), (nl1++nl2++nl3++nl4++nl5)~(ml1++ml2++ml3++ml4++ml5)  -> (nl1 ++nl4++nl2++nl5++nl3)~ (ml1 ++ml4++ml2++ml5++ml3).**)

(*********************Axiliary axioms****************************)

(*Axiom simpinsub_B : forall (n n1 n2 n3 n4 n5 n6 :nat)(t1 t2 : Bool), (ifb (Bvar n) [n5 := ifb TRue (Bvar n1) (Bvar n2)](t1)
   [n6 := ifb FAlse (Bvar n3) (Bvar n4)](t2))## (ifb (Bvar n) [n5 := Bvar n1](t1) [n6 := Bvar n4](t2)).**)
*) 

(*
Section dh_axioms.
 *) 
(** [DDH] assumption:
[[
    Fresh [n,n1,n2,n3]-> [G(n), g(n),g(n)^(r (n1)),g(n)^(r (n2)), g(n)^(r (n1))(r (n2))] ~[G(n), g(n),g(n)^(r (n1)),g(n)^(r (n2)), g(n)^(r (n3))]
]] 

*)
     (*
Axiom DDH : forall (n n1 n2 n3: nat),  (Fresh [ n , n1 ,  n2  , n3 ] []) = true-> 
                                       [ msg (G n) , msg (g n) , msg (exp (G n) (g n) (r  n1)) , msg (exp (G n) (g n) (r  n2)) , msg (exp (G n) (exp (G n) (g n) (r  n1)) (r  n2))] ~ [msg (G n) , msg (g n) , msg (exp (G n) (g n) (r  n1)) , msg (exp (G n) (g n) (r n2)) , msg (exp (G n) (g n) (r n3))] .

End dh_axioms.
*)
Section ds_axioms.
(** * Digital Signatures*)
(** Correctness *)

Axiom correctness :  forall (n:nat) (t t' :message), (ver (vk n)  t (sign (ssk n) t t')) ## TRue.
 

(** Existential unforgeability under adaptively chosen message attacks (UF-CMA secure) *)

  Fixpoint unforgb  (j:nat) (n:nat)  (ml: list message) (t u :message) : Bool :=
    match j, ml with
      |  0 , _ => FAlse
      |  S _, [ ] => FAlse             
      | S j',  h :: tl => match h with
                             | (sign (pi2 (ks (N n))) t1 t2) =>   IF (eqm t t1) then (ver (vk n) t1 u) else (unforgb j' n tl t u)
                             | _ => FAlse
                           end
    end.    

  Axiom UFCMA : forall (n :nat)(t u: message), (closMylist [msg t, msg u] = true) /\ (insec_n_mylis n [msg t, msg u] = false) ->
                                               let j := length(list_skn_in_sign n ((subtrmls_msg t) ++ (subtrmls_msg u))) in
                                               let ml := distsigntrms n ((subtrmls_msg t) ++ ( subtrmls_msg u)) in
                                               (ver (vk n) t u) ## (unforgb j n ml t u).
 
End ds_axioms.
