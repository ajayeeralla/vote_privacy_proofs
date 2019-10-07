(************************************************************************)
(* Copyright (c) 2017-2018, Ajay Kumar Eeralla <ae266@mail.missouri.edu>*)     
(************************************************************************) 

Require Export tactics.
 
(** * FOO Protocol *)
Section foo_axioms.
  (** Bindness Axiom *)
Definition r (n:nat) := rb (N n).
  
(*Definition distvars {n} (l :mylist n) := nodup (mvars_mylis  l).*)

Notation "'[' x '<-' s ']' l" :=  (submsg_mylist x s l).
(** ** Trapdoor Commitments *) 
  (** * [COMMEQL] *)
 
 Definition k (n:nat) := kc (N n).

 Axiom commEql: forall (n1 n2:nat) (t1 t2 : message), closMylist [msg t1, msg t2] = true /\ (Fresh (cons n1 nil) [msg t1, msg t2]) = true -> (Fresh (cons n2 nil) [msg t1, msg t2]) = true -> (IF |t1| #? |t2| then |(comm t1 (k n1))|#? |(comm t2 (k n2))| else TRue) ## TRue.
  (** * [COMMKEYEQL] *)           
   Axiom commKeyEql: forall (n1 n2:nat),  (|(k n1)|#?|(k n2)|) ## TRue.

   (** * [Computational Hiding] *) 
   (** * [COMPHID] *)
   Axiom compHid: forall (n1 n2:nat) (t t1 t2 : message) {n} (z: mylist n), closMylist [msg t, msg t1, msg t2] = true /\ closMylist z = true /\ Fresh [n1; n2] ([msg t, msg t1, msg t2]++z) = true ->
                                                                            (z ++ [msg (If |t1|#?|t2| then ((comm t1 (k n1)), (comm t2 (k n2))) else t)]) ~ (z ++ [msg (If |t1|#?|t2| then ((comm t2 (k n1)), (comm t1 (k n2))) else t)]).
Eval compute in ([0<- O] [msg O]).
   
   Axiom compHid_ext: forall (n2 n3 n4 n5:nat) (t2 t3 : message) {n} {m} (z: mylist n) (l:mylist m), closMylist [msg t2, msg t3] = true /\ closMylist z = true /\ Fresh [n2; n3] (z++[msg t2, msg t3]) = true /\ (|t2|#?|t3|) ## TRue ->
                                                                                ((length (distMvars l))=? 2)%nat = true -> 
                                                                                let mvl:= [n4; n5] in ((distMvars l) = mvl \/ (distMvars l) = [n5; n4])  ->
                                                                                                        
                                                                                                         let m0 := (comm t2 (k n2)) in
                                                                                                         let m1 := (comm t3 (k n3)) in
                                                                                                         let m0':= (comm t3 (k n2)) in
                                                                                                         let m1':= (comm t2 (k n3)) in 
                                                                                                                                                          
(z ++ ([n4 <- m0]([n5 <- m1]l))) ~ (z ++ ([n4 <- m0']([n5 <- m1'] l))).



(** [BLINDNESS] *)

Axiom blindness: forall (n0 n1 n2 n3:nat) {n} (m0 m1 t t0 t1 : message) (z: mylist n),
    (Fresh [n0; n1] (z ++[msg t, msg m0, msg m1, msg t0 , msg t1]) = true) ->  closMylist (z++ [msg t, msg m0, msg m1]) = true ->   ((length (distMvars [msg t0, msg t1]))=? 2)%nat = true -> 
    let mvl:= [n2; n3] in  (mVarMsg t0) = mvl /\ (mVarMsg t1) = mvl ->
                 let r0 := (r n0) in
                 let r1 := (r n1) in
                 let t2 := ({{ n2 := (bl m0 t r0) }} ({{ n3:=(bl m1 t r1) }} t0)) in
                 let t3 := ({{ n2 := (bl m0 t r0) }} ({{ n3:=(bl m1 t r1) }} t1)) in
                 let t4 := ({{ n2 := (bl m1 t r0) }} ({{ n3:=(bl m0 t r1) }} t0)) in
                 let t5 := ({{ n2 := (bl m1 t r0) }} ({{ n3:=(bl m0 t r1) }} t1)) in
                 let pair1 := ((ub m0 t r0 t2), (ub m1 t r1 t3)) in
                 let pair2 := ((ub m0 t r1 t5), (ub m1 t r0 t4)) in             
                 (z ++ [msg (bl m0 t r0), msg (bl m1 t r1), msg (If (acc m0 t r0 t2)& (acc m1 t r1 t3) then pair1 else (|_, |_)) ])
                    ~
                   
                  (z ++ [msg (bl m1 t r0), msg (bl m0 t r1), msg (If (acc m1 t r0 t4)& (acc m0 t r1 t5) then pair2 else (|_, |_))]). 

Axiom ubNotUndefined: forall (n0 n1 n2 n3:nat) (t t0 t1 t2 : message), closMylist [msg t, msg t0] = true -> 
                                                                 (Fresh [n0; n1] [msg t, msg t0, msg t1, msg t2] = true) ->
                                                                 let mvl := [n2; n3] in (mVarMsg t2) = mvl ->
                                                                                        let r1 := (r n0) in
                                                                                        let r2 := (r n1) in
                                                                 let t4:= ({{ n2 := (bl t1 t r2)  }} ({{n3:=(bl t0 t r1)  }} t2)) in

                                                                 (IF (acc t0 t r1 t4) then (ub t0 t r1 t4)#?|_ else FAlse) ## FAlse. 

Axiom ubNotUndefined2: forall (n0 n1 n2 n3:nat) (t t0 t1 t2 : message), closMylist [msg t, msg t0] = true -> 
                                                                 (Fresh [n0; n1] [msg t, msg t0, msg t1, msg t2] = true) ->
                                                                 let mvl := [n2; n3] in (mVarMsg t2) = mvl ->
                                                                                        let r1 := (r n0) in
                                                                                        let r2 := (r n1) in
                                                                 let t4:= ({{ n2 := (bl t0 t r1)}} ({{n3:=(bl t1 t r2)}} t2)) in

                                                                 (IF (acc t0 t r1 t4) then (ub t0 t r1 t4)#?|_ else FAlse) ## FAlse.





 

Axiom ubEql: forall (n0 n1 n3 n4:nat) (t t0 t1 t2 t3: message), closMylist [msg t, msg t0, msg t1] = true -> (occur_name_msg n0 t2) = false -> (occur_name_msg n1 t3) = false ->
                                                                 (Fresh (cons n0 nil) [msg t, msg t0, msg t3] = true)%nat -> (Fresh (cons n1 nil) [msg t, msg t1, msg t2] = true) -> (|t0|#?|t1|) ## TRue -> 

                                                                let mvl := [n3;n4] in (mVarMsg t2) = mvl /\ (mVarMsg t3) = mvl ->                                                                                            
                                                                                            let r0:= (r n0) in 
                                                                                            let r1:= (r n1) in 
                                                                                            let t4:= ({{ n3 := (bl t0 t r0) }} ({{ n4 := (bl t1 t r1) }} t2)) in
                                                                                            let t5:= ({{ n3 := (bl t0 t r0) }} ({{ n4 := (bl t1 t r1) }} t3)) in

                                                                                            (IF (acc t0 t r0 t4)& (acc t1 t r1 t5) then |(ub t0 t r0 t4)|#?|(ub t1 t r1 t5)| else TRue) ## TRue.

(** * Mix-net Server *)
(** There are six permutations possible on element set *)

Axiom shuffle1: forall (t1 t2 t3: message), (shufl t1 t2 t3) # (shufl t1 t2 t3).
Axiom shuffle2: forall (t1 t2 t3: message), (shufl t1 t2 t3) # (shufl t1 t3 t2).    
Axiom shuffle3: forall (t1 t2 t3: message), (shufl t1 t2 t3) # (shufl t2 t1 t3).                                                                                                           
Axiom shuffle4: forall (t1 t2 t3: message), (shufl t1 t2 t3) # (shufl t2 t3 t1).
Axiom shuffle5: forall (t1 t2 t3: message), (shufl t1 t2 t3) # (shufl t3 t1 t2).
Axiom shuffle6: forall (t1 t2 t3: message), (shufl t1 t2 t3) # (shufl t3 t2 t1).

(** * Further length regularity *)

Axiom pairEql: forall (x1 x2 y1 y2: message), (IF (|x1|#? |y1|)& (|x2|#? |y2|) then (|(x1, x2)|#? |(y1, y2)|) else TRue) ## TRue.

Axiom candEql1: (|C1|#?|C2|) ## TRue.
Axiom candEql2: (|C1|#?|C3|) ## TRue.
Axiom candEql3: (|C2|#?|C3|) ## TRue.

Axiom phaseEql: (|TWO|#?|THREE|) ## TRue.

Axiom zeroEql: forall x, (|z(x)|#? |x|) ## TRue.

(** * Distinctness of Constants *)

Axiom agentDist1: (|A|#?|B|) ## FAlse.
Axiom agentDist2: (|A|#?|M|) ## FAlse.
Axiom agentDist3: (|B|#?|M|) ## FAlse.

Axiom phaseDist: (|TWO|#?|THREE|) ## FAlse.
End foo_axioms.
