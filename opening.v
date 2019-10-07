Require Export voting.
Set Nested Proofs Allowed.
(** [Opening Phase] *)
(** STEP:6 *)

Definition dist1 x (n n':nat) := let x := (pi1 (x n n')) in (dist (tau 1 x) (tau 2 x) (tau 3 x)).

Definition dist2 x (n n':nat) := let x := (pi2 (x n n')) in (dist (tau 1 x) (tau 2 x) (tau 3 x)).

Definition distbb x n n' := (dist1 x n n') & (dist2 x n n').

(** x6 **) 
Definition x6t (n n':nat) := f (toListm (phi0 ++ [msg (tr 0 n 3  5 9), msg (tr 1 n' 4 6 10), msg (e n 3 5 (x3tt 0 1) TWO 11), msg (e n' 4 6 (x4ttt n n') TWO  12), msg (strm (x5t n n')) ])).
Definition x6ft (n n':nat) := f (toListm (phi0 ++ [msg (tr 1 n' 4 6 10), msg (tr 0 n 3 5 9), msg (e n' 4 6 (x3tt 0 1) TWO 11), msg (e n 3 5 (x4fttt n n') TWO 12), msg (strm (x5ft n n'))])).

Definition theta21 x a n n' := ((to (x n n')) #? a) & (distbb x n n').
 
Definition acc1 n n' k r   := (acpt n k r (x3tt n n')). (**or (acpt n k r (x4ttt n n')).*)
Definition acc2 n n' k r   := (acpt n' k r (x3tt n n')). (** or (acpt n' k r (x4ttt n n'))*)

Definition e1 n k x (n':nat) n3 := (enc ((label (c n k) (x n n')), ((kc (N k)) , THREE)) (pke 2) (se n3)).
Eval compute in bcheck.

(** previous terms *)

Definition t61 (n n' k r:nat) := (If (mchecks x5t n n' TWO) then (If (theta21 x6t A n n') then (If (acc1 n n' k r)& (bcheck (c n k) (x6t n n')) then (e1 n k x6t n' 13) else O) else O) else O).

Definition t62 (n n' k r:nat) := (If (mchecks x5ft n n' TWO) then (If (theta21 x6ft B n n') then (If (acc2 n n' k r)& (bcheck (c n' k) (x6ft n n')) then (e1 n' 4 x6ft n' 13) else O) else O) else O).

Definition t4ss n n' := If (theta x1 A) then
                         (If (theta (x2t n) B) then
                            (If ((to (x3tt n n')) #? A) then
                               (If (acpt n 3 5 (x3tt n n')) then
                                  (If ((to (x4ttt n n')) #? B) then
                                     (If (acpt n' 4 6 (x4ttt n n')) then (t61 n n' 3 5)
                                      else O)
                                   else O) else O) else O) else O)
                        else (If (theta x1 B) then
                                (If (theta (x2ft n') A) then
                                   (If ((to (x3ftt n n'))#?B) then
                                      (If (acpt n' 4 6 (x3ftt n n')) then
                                         (If ((to (x4fttt n n'))#? A) then
                                            (If (acpt n 3 5 (x4fttt n n')) then (t62 n n' 4 6) else O) else O) else O) else O) else O) else O).
(*********************************)

Definition phi6 n n' := (phi5 n n') ++ [msg (t4ss n n')].

(** STEP:7 *)

Definition x7t (n n':nat) := f (toListm (phi0 ++ [msg (tr 0 n 3  5 9), msg (tr 1 n' 4 6 10), msg (e n 3 5 (x3tt 0 1) TWO 11), msg (e n' 4 6 (x4ttt n n') TWO  12), msg (strm (x5t n n')), msg (e1 n 3 x6t n' 13) ])).
Definition x7ft (n n':nat) := f (toListm (phi0 ++ [msg (tr 1 n' 4 6 10), msg (tr 0 n 3 5 9), msg (e n' 4 6 (x3tt 0 1) TWO 11), msg (e n 3 5 (x4fttt n n') TWO 12), msg (strm (x5ft n n')), msg (e1 n' 4 x6ft n' 13)])).

Definition t71 (n n':nat) := (If (theta21 x7t B n n') then (If (acc1 n n' 4 6)& (bcheck (c n' 4) (x7t n n')) then (e1 n 4 x7t n' 14) else O) else O).

Definition t72 (n n':nat) := (If (theta21 x7ft A n n') then (If (acc2 n n' 3 5)& (bcheck (c n' 3) (x7ft n n')) then (e1 n' 3 x6ft n' 14) else O) else O).
 
Definition t61s (n n' k r:nat) := (If (mchecks x5t n n' TWO) then (If (theta21 x6t A n n') then (If (acc1 n n' k r)& (bcheck (c n k) (x6t n n')) then (t71 n n') else O) else O) else O).

Definition t62s (n n' k r:nat) := (If (mchecks x5ft n n' TWO) then (If (theta21 x6ft B n n') then (If (acc2 n n' k r)& (bcheck (c n' k) (x6ft n n')) then (t72 n n') else O) else O) else O).

Definition t47 n n' := If (theta x1 A) then
                         (If (theta (x2t n) B) then
                            (If ((to (x3tt n n')) #? A) then
                               (If (acpt n 3 5 (x3tt n n')) then
                                  (If ((to (x4ttt n n')) #? B) then
                                     (If (acpt n' 4 6 (x4ttt n n')) then (t61s n n' 3 5)
                                      else O)
                                   else O) else O) else O) else O)
                      else (If (theta x1 B) then
                              (If (theta (x2ft n') A) then
                                 (If ((to (x3ftt n n'))#?B) then
                                    (If (acpt n' 4 6 (x3ftt n n')) then
                                       (If ((to (x4fttt n n'))#? A) then
                                          (If (acpt n 3 5 (x4fttt n n')) then (t62s n n' 4 6) else O) else O) else O) else O) else O) else O).
Definition phi7 n n' := (phi6 n n') ++ [msg (t47 n n')].

(** STEP:8 *)

 Definition x8t (n n':nat) := f (toListm (phi0 ++ [msg (tr 0 n 3  5 9), msg (tr 1 n' 4 6 10), msg (e n 3 5 (x3tt 0 1) TWO 11), msg (e n' 4 6 (x4ttt n n') TWO  12), msg (strm (x5t n n')), msg (e1 n 3 x6t n' 13), msg (e1 n 4 x7t n' 14) ])).
Definition x8ft (n n':nat) := f (toListm (phi0 ++ [msg (tr 1 n' 4 6 10), msg (tr 0 n 3 5 9), msg (e n' 4 6 (x3tt 0 1) TWO 11), msg (e n 3 5 (x4fttt n n') TWO 12), msg (strm (x5ft n n')), msg (e1 n' 4 x6ft n' 13), msg (e1 n' 3 x6ft n' 14)])).
Eval compute in mchecks.

Definition theta23 x (n n':nat) := let D := ( (d 1 (x n n')), ((d 2 (x n n')), (d 3 (x n n')))) in
                             let kOcc := (isin (bk 3) D) & (isin (bk 4) D) in
                             let kdnOcc := !(isin (bk 3) D) or !(isin (bk 4) D) in
                                   (mchecks x n n' THREE)& (kOcc or kdnOcc).

Definition fintrm x n n' := (If (theta23 x n n') then (strm (x n n'))  else O).

Definition t71s (n n':nat) := (If (theta21 x7t B n n') then (If (acc1 n n' 4 6)& (bcheck (c n' 4) (x7t n n')) then (fintrm x7t n n') else O) else O).

Definition t72s (n n':nat) := (If (theta21 x7ft A n n') then (If (acc2 n n' 3 5)& (bcheck (c n' 3) (x7ft n n')) then (fintrm x7ft n n') else O) else O).

 
Definition t61ss (n n' k r:nat) := (If (mchecks x5t n n' TWO) then (If (theta21 x6t A n n') then (If (acc1 n n' k r)& (bcheck (c n k) (x6t n n')) then (t71s n n') else O) else O) else O).

Definition t62ss (n n' k r:nat) := (If (mchecks x5ft n n' TWO) then (If (theta21 x6ft B n n') then (If (acc2 n n' k r)& (bcheck (c n' k) (x6ft n n')) then (t72s n n') else O) else O) else O).

Definition t48 n n' := If (theta x1 A) then
                         (If (theta (x2t n) B) then
                            (If ((to (x3tt n n')) #? A) then
                               (If (acpt n 3 5 (x3tt n n')) then
                                  (If ((to (x4ttt n n')) #? B) then
                                     (If (acpt n' 4 6 (x4ttt n n')) then (t61ss n n' 3 5)
                                      else O)
                                   else O) else O) else O) else O)
 else (If (theta x1 B) then
         (If (theta (x2ft n') A) then
            (If ((to (x3ftt n n'))#?B) then
               (If (acpt n' 4 6 (x3ftt n n')) then
                  (If ((to (x4fttt n n'))#? A) then
                     (If (acpt n 3 5 (x4fttt n n')) then (t62ss n n' 4 6) else O) else O) else O) else O) else O) else O).

 Definition phi8 n n' := (phi7 n n') ++ [msg (t48 n n')].

  Theorem frame6TraceInd:
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
   bol ((tau 3 u)#? TWO) & ((tau 3 v) #? TWO) & ((tau 3 (dec (tau 3 (x5t 0 1)) (ske 2))) #? TWO), msg (shufl ((tau 1 u), (tau 2 u)) ((tau 1 v), (tau 2 v)) ((tau 1 (dec (tau 3 (x5t 0 1)) (ske 2))),  (tau 2 (dec (tau 3 (x5t 0 1)) (ske 2))))), bol ((to (x6t 0 1)) #? A) & (distbb x6t 0 1), bol (acc1 0 1 3 5)& (bcheck (c 0 3) (x6t 0 1)), msg (e1 0 3 x6t 1 13)] ~

[msg A, msg B, msg M, msg C1, msg C2, msg C3, msg ONE, msg TWO, msg THREE, msg (vk 0), msg (vk 1), 
   msg (pke 2), bol (theta x1 A), msg (tr 0 1 3 5 9), bol (theta (x2t 1) B), msg (tr 1 0 4 6 10), 
   bol (to (x3tt 1 0)) #? A, bol (acpt 1 3 5 (x3tt 1 0)),
   msg {u'}_2 ^^ 11, bol (to (x4ttt 1 0)) #? B,
   bol (acpt 0 4 6 (x3tt 1 0)), msg {v'}_ 2 ^^ 12,
   bol (to (x5t 1 0)) #? M, bol (tau 1 (x5t 1 0)) #? {u'}_ 2 ^^ 11,
   bol (tau 2 (x5t 1 0)) #? {v'}_ 2 ^^ 12,
   bol (!((tau 3 (x5t 1 0)) #? {u'}_ 2 ^^ 11)) & (! ((tau 3 (x5t 1 0)) #? {v'}_ 2 ^^ 12)),
   bol ((tau 3 u')#? TWO) & ((tau 3 v') #? TWO) & ((tau 3 (dec (tau 3 (x5t 1 0)) (ske 2))) #? TWO), msg (shufl ((tau 1 u'), (tau 2 u')) ((tau 1 v'), (tau 2 v')) ((tau 1 (dec (tau 3 (x5t 1 0)) (ske 2))),  (tau 2 (dec (tau 3 (x5t 1 0)) (ske 2))))), bol ((to (x6t 1 0)) #? A) & (distbb x6t 1 0), bol (acc1 1 1 3 5)& (bcheck (c 1 3) (x6t 1 0)), msg (e1 1 3 x6t 0 13)].

Proof. simpl.
repeat rewrite proj1, proj2. unfold bcheck. unfold isin.

Admitted.

  
  Theorem frame7TraceInd:
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
   bol ((tau 3 u)#? TWO) & ((tau 3 v) #? TWO) & ((tau 3 (dec (tau 3 (x5t 0 1)) (ske 2))) #? TWO), msg (shufl ((tau 1 u), (tau 2 u)) ((tau 1 v), (tau 2 v)) ((tau 1 (dec (tau 3 (x5t 0 1)) (ske 2))),  (tau 2 (dec (tau 3 (x5t 0 1)) (ske 2))))), bol ((to (x6t 0 1)) #? A) & (distbb x6t 0 1), bol (acc1 0 1 3 5)& (bcheck (c 0 3) (x6t 0 1)), msg (e1 0 3 x6t 1 13), bol ((to (x7t 0 1)) #? B) & (distbb x7t 0 1), bol (acc2 0 1 4 6)& (bcheck (c 1 4) (x7t 0 1)), msg (e1 0 4 x7t 1 14)] ~

[msg A, msg B, msg M, msg C1, msg C2, msg C3, msg ONE, msg TWO, msg THREE, msg (vk 0), msg (vk 1), 
   msg (pke 2), bol (theta x1 A), msg (tr 0 1 3 5 9), bol (theta (x2t 1) B), msg (tr 1 0 4 6 10), 
   bol (to (x3tt 1 0)) #? A, bol (acpt 1 3 5 (x3tt 1 0)),
   msg {u'}_2 ^^ 11, bol (to (x4ttt 1 0)) #? B,
   bol (acpt 0 4 6 (x3tt 1 0)), msg {v'}_ 2 ^^ 12,
   bol (to (x5t 1 0)) #? M, bol (tau 1 (x5t 1 0)) #? {u'}_ 2 ^^ 11,
   bol (tau 2 (x5t 1 0)) #? {v'}_ 2 ^^ 12,
   bol (!((tau 3 (x5t 1 0)) #? {u'}_ 2 ^^ 11)) & (! ((tau 3 (x5t 1 0)) #? {v'}_ 2 ^^ 12)),
   bol ((tau 3 u')#? TWO) & ((tau 3 v') #? TWO) & ((tau 3 (dec (tau 3 (x5t 1 0)) (ske 2))) #? TWO), msg (shufl ((tau 1 u'), (tau 2 u')) ((tau 1 v'), (tau 2 v')) ((tau 1 (dec (tau 3 (x5t 1 0)) (ske 2))),  (tau 2 (dec (tau 3 (x5t 1 0)) (ske 2))))), bol ((to (x6t 1 0)) #? A) & (distbb x6t 1 0), bol (acc1 1 1 3 5)& (bcheck (c 1 3) (x6t 1 0)), msg (e1 1 3 x6t 0 13), bol ((to (x7t 1 0)) #? B) & (distbb x7t 1 0), bol (acc2 1 0 4 6)& (bcheck (c 0 4) (x7t 1 0)), msg (e1 1 4 x7t 0 14)].
unfold e1.
 Theorem frame8TraceInd:
                let u:= (c 0 3, (ub (c 0 3) pk (bk 5) (x3tt 0 1), TWO)) in
                let u':= (c 1 3, (ub (c 1 3) pk (bk 5) (x3tt 1 0), TWO)) in
                let v:= (c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO)) in
                let v':= (c 0 4, (ub (c 0 4) pk (bk 6) (x3tt 1 0), TWO)) in
                let u1 := (label (c 0 3) (x6t 0 1), (kc (N 3), THREE)) in
                let v1:= (label (c 0 4) (x7t 0 1), (kc (N 4), THREE)) in
                let u1' := (label (c 1 3) (x6t 1 0), (kc (N 3), THREE)) in
                let v1' := (label (c 1 4) (x7t 1 0), (kc (N 4), THREE)) in 
   [msg A, msg B, msg M, msg C1, msg C2, msg C3, msg ONE, msg TWO, msg THREE, msg (vk 0), msg (vk 1), 
   msg (pke 2), bol (theta x1 A), msg (tr 0 0 3 5 9), bol (theta (x2t 0) B), msg (tr 1 1 4 6 10), 
   bol (to (x3tt 0 1)) #? A, bol (acpt 0 3 5 (x3tt 0 1)),
   msg {u}_ 2 ^^ 11, bol (to (x4ttt 0 1)) #? B,
   bol (acpt 1 4 6 (x3tt 0 1)), msg {v}_ 2 ^^ 12,
   bol (to (x5t 0 1)) #? M, bol (tau 1 (x5t 0 1)) #? {u}_ 2 ^^ 11,
   bol (tau 2 (x5t 0 1)) #? {v}_ 2 ^^ 12,
   bol (!((tau 3 (x5t 0 1)) #? {u}_ 2 ^^ 11)) & (!((tau 3 (x5t 0 1)) #? {v}_ 2 ^^ 12)),
   bol ((tau 3 u)#? TWO) & ((tau 3 v) #? TWO) & ((tau 3 (dec (tau 3 (x5t 0 1)) (ske 2))) #? TWO), msg (shufl ((tau 1 u), (tau 2 u)) ((tau 1 v), (tau 2 v)) ((tau 1 (dec (tau 3 (x5t 0 1)) (ske 2))),  (tau 2 (dec (tau 3 (x5t 0 1)) (ske 2))))), bol ((to (x6t 0 1)) #? A) & (distbb x6t 0 1), bol (acc1 0 1 3 5)& (bcheck (c 0 3) (x6t 0 1)), msg (e1 0 3 x6t 1 13), bol ((to (x7t 0 1)) #? B) & (distbb x7t 0 1), bol (acc2 0 1 4 6)& (bcheck (c 1 4) (x7t 0 1)), msg (e1 0 4 x7t 1 14),  bol (to (x8t 0 1)) #? M, bol (tau 1 (x8t 0 1)) #? {u1}_ 2 ^^ 11,
   bol (tau 2 (x8t 0 1)) #? {v1}_ 2 ^^ 12,
   bol (!((tau 3 (x8t 0 1)) #? {u1}_ 2 ^^ 11)) & (!((tau 3 (x8t 0 1)) #? {v1}_ 2 ^^ 12)), msg (If (let D := ((d 1 (x8t 0 1)), ((d 2 (x8t 0 1)), (d 3 (x8t 0 1)))) in
                             let kOcc := (isin (bk 3) D) & (isin (bk 4) D) in
                             let kdnOcc := !(isin (bk 3) D) or !(isin (bk 4) D) in
                                   (mchecks x8t 0 1 THREE)& (kOcc or kdnOcc)) then  (shufl ((tau 1 u1), (tau 2 u1)) ((tau 1 v1), (tau 2 v1)) ((tau 1 (dec (tau 3 (x8t 0 1)) (ske 2))),  (tau 2 (dec (tau 3 (x8t 0 1)) (ske 2))))) else O) ] ~

[msg A, msg B, msg M, msg C1, msg C2, msg C3, msg ONE, msg TWO, msg THREE, msg (vk 0), msg (vk 1), 
   msg (pke 2), bol (theta x1 A), msg (tr 0 1 3 5 9), bol (theta (x2t 1) B), msg (tr 1 0 4 6 10), 
   bol (to (x3tt 1 0)) #? A, bol (acpt 1 3 5 (x3tt 1 0)),
   msg {u'}_2 ^^ 11, bol (to (x4ttt 1 0)) #? B,
   bol (acpt 0 4 6 (x3tt 1 0)), msg {v'}_ 2 ^^ 12,
   bol (to (x5t 1 0)) #? M, bol (tau 1 (x5t 1 0)) #? {u'}_ 2 ^^ 11,
   bol (tau 2 (x5t 1 0)) #? {v'}_ 2 ^^ 12,
   bol (!((tau 3 (x5t 1 0)) #? {u'}_ 2 ^^ 11)) & (! ((tau 3 (x5t 1 0)) #? {v'}_ 2 ^^ 12)),
   bol ((tau 3 u')#? TWO) & ((tau 3 v') #? TWO) & ((tau 3 (dec (tau 3 (x5t 1 0)) (ske 2))) #? TWO), msg (shufl ((tau 1 u'), (tau 2 u')) ((tau 1 v'), (tau 2 v')) ((tau 1 (dec (tau 3 (x5t 1 0)) (ske 2))),  (tau 2 (dec (tau 3 (x5t 1 0)) (ske 2))))), bol ((to (x6t 1 0)) #? A) & (distbb x6t 1 0), bol (acc1 1 1 3 5)& (bcheck (c 1 3) (x6t 1 0)), msg (e1 1 3 x6t 0 13), bol ((to (x7t 1 0)) #? B) & (distbb x7t 1 0), bol (acc2 1 0 4 6)& (bcheck (c 0 4) (x7t 1 0)), msg (e1 1 4 x7t 0 14), bol (to (x5t 1 0)) #? M, bol (tau 1 (x8t 1 0)) #? {u1'}_ 2 ^^ 13,
   bol (tau 2 (x8t 1 0)) #? {v1'}_ 2 ^^ 14,
   bol (!((tau 3 (x8t 1 0)) #? {u1'}_ 2 ^^ 13)) & (! ((tau 3 (x8t 1 0)) #? {v1'}_ 2 ^^ 14)),   msg (If 
   (let D := ((d 1 (x8t 1 0)), ((d 2 (x8t 1 0)), (d 3 (x8t 1 0)))) in
                             let kOcc := (isin (bk 3) D) & (isin (bk 4) D) in
                             let kdnOcc := !(isin (bk 3) D) or !(isin (bk 4) D) in
                             (mchecks x8t 1 0 THREE)& (kOcc or kdnOcc)) then (shufl ((tau 1 u1'), (tau 2 u1')) ((tau 1 v1'), (tau 2 v1')) ((tau 1 (dec (tau 3 (x8t 1 0)) (ske 2))),  (tau 2 (dec (tau 3 (x8t 1 0)) (ske 2))))) else O)].
 Proof.


   Proof. simpl.  repeat rewrite proj1, proj2.
Axiom eqmref: forall m, m#?m ## TRue. 
          rewrite eqmref. 
repeat rewrite andB_TRue_l.  unfold mchecks.
unfold d. unfold distbb. unfold dist1, dist2. unfold strm. unfold p. unfold d.
(** (tau 1 (x8t 1 0)) = (e1 1 3 x6t 0 13), (tau 2 (x8t 1 0)) = (e1 1 4 x7t 0 14) and (tau 3 (x8t 1 0)) != (e1 1 3 x6t 0 13) or (e1 1 4 x7t 0 14) *)
 
unfold e1.

Theorem frame9ind: 
[msg A, msg B, msg M, msg C1, msg C2, msg C3, msg ONE, msg TWO, msg THREE, msg (vk 0), msg (vk 1), 
   msg (pke 2), bol (theta x1 A), msg (tr 0 0 3 5 9), bol (theta (x2t 0) B), msg (tr 1 1 4 6 10), bol (to (x3tt 0 1)) #? A,
   bol (acpt 0 3 5 (x3tt 0 1)), msg {(c 0 3, (ub (c 0 3) pk (bk 5) (x3tt 0 1), TWO)) }_ 2 ^^ 11, bol (to (x4ttt 0 1)) #? B,
   bol (acpt 1 4 6 (x3tt 0 1)), msg {(c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO)) }_ 2 ^^ 12, bol (to (x5t 0 1)) #? M,
   bol (pi1 (x5t 0 1)) #? {(c 0 3, (ub (c 0 3) pk (bk 5) (x3tt 0 1), TWO)) }_ 2 ^^ 11,
   bol (pi1 (pi2 (x5t 0 1))) #? {(c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO)) }_ 2 ^^ 12,
   bol
     (! ((pi2 (pi2 (x5t 0 1))) #? {(c 0 3, (ub (c 0 3) pk (bk 5) (x3tt 0 1), TWO)) }_ 2 ^^ 11)) &
     ! ((pi2 (pi2 (x5t 0 1))) #? {(c 1 4, (ub (c 1 4) pk (bk 6) (x3tt 0 1), TWO)) }_ 2 ^^ 12),
   bol (pi2 (pi2 (dec (pi2 (pi2 (x5t 0 1))) (ske 2)))) #? TWO,
   msg
     (shufl (c 0 3, ub (c 0 3) pk (bk 5) (x3tt 0 1)) (c 1 4, ub (c 1 4) pk (bk 6) (x3tt 0 1))
        (pi1 (dec (pi2 (pi2 (x5t 0 1))) (ske 2)), pi1 (pi2 (dec (pi2 (pi2 (x5t 0 1))) (ske 2))))),
   bol
     ((to (x6t 0 1)) #? A) &
     (dist (tau 1 (pi1 (x6t 0 1))) (tau 2 (pi1 (x6t 0 1))) (tau 3 (pi1 (x6t 0 1)))) &
     (dist (tau 1 (pi2 (x6t 0 1))) (tau 2 (pi2 (x6t 0 1))) (tau 3 (pi2 (x6t 0 1)))),
   bol (acc1 0 1 3 5) & (bcheck (c 0 3) (x6t 0 1)), msg {(label (c 0 3) (x6t 0 1), (kc (N 3), THREE)) }_ 2 ^^ 13,
   bol
     ((to (x7t 0 1)) #? B) &
     (dist (tau 1 (pi1 (x7t 0 1))) (tau 2 (pi1 (x7t 0 1))) (tau 3 (pi1 (x7t 0 1)))) &
     (dist (tau 1 (pi2 (x7t 0 1))) (tau 2 (pi2 (x7t 0 1))) (tau 3 (pi2 (x7t 0 1)))),
   bol (acc2 0 1 4 6) & (bcheck (c 1 4) (x7t 0 1)), msg {(label (c 0 4) (x7t 0 1), (kc (N 4), THREE)) }_ 2 ^^ 14,
   bol
     ((dist (dec (tau 1 (x8t 0 1)) (ske 2)) (dec (tau 2 (x8t 0 1)) (ske 2)) (dec (tau 3 (x8t 0 1)) (ske 2))) &
      (pchecks (x8t 0 1) THREE)) &
     ((isin (bk 3) (dec (tau 1 (x8t 0 1)) (ske 2), (dec (tau 2 (x8t 0 1)) (ske 2), dec (tau 3 (x8t 0 1)) (ske 2)))) &
      (isin (bk 4) (dec (tau 1 (x8t 0 1)) (ske 2), (dec (tau 2 (x8t 0 1)) (ske 2), dec (tau 3 (x8t 0 1)) (ske 2))))) or
     (! (isin (bk 3) (dec (tau 1 (x8t 0 1)) (ske 2), (dec (tau 2 (x8t 0 1)) (ske 2), dec (tau 3 (x8t 0 1)) (ske 2))))) or
     ! (isin (bk 4) (dec (tau 1 (x8t 0 1)) (ske 2), (dec (tau 2 (x8t 0 1)) (ske 2), dec (tau 3 (x8t 0 1)) (ske 2)))), bol (tau 1 (x8t 0 1))#?{(label (c 1 3) (x6t 1 0), (kc (N 3), THREE)) }_ pke 2 ^^ (se 13), bol (tau 2 (x8t 1 0))#?
   msg
     (shufl (tau 1 (dec (tau 1 (x8t 0 1)) (ske 2)), tau 2 (dec (tau 1 (x8t 0 1)) (ske 2)))
        (tau 1 (dec (tau 2 (x8t 0 1)) (ske 2)), tau 2 (dec (tau 2 (x8t 0 1)) (ske 2)))
        (tau 1 (dec (tau 3 (x8t 0 1)) (ske 2)), tau 2 (dec (tau 3 (x8t 0 1)) (ske 2))))] ~
  [msg A, msg B, msg M, msg C1, msg C2, msg C3, msg ONE, msg TWO, msg THREE, msg (vk 0), msg (vk 1), 
  msg (pke 2), bol (theta x1 A), msg (tr 0 1 3 5 9), bol (theta (x2t 1) B), msg (tr 1 0 4 6 10), bol (to (x3tt 1 0)) #? A,
  bol (acpt 1 3 5 (x3tt 1 0)), msg {(c 1 3, (ub (c 1 3) pk (bk 5) (x3tt 1 0), TWO)) }_ 2 ^^ 11, bol (to (x4ttt 1 0)) #? B,
  bol (acpt 0 4 6 (x3tt 1 0)), msg {(c 0 4, (ub (c 0 4) pk (bk 6) (x3tt 1 0), TWO)) }_ 2 ^^ 12, bol (to (x5t 1 0)) #? M,
  bol (pi1 (x5t 1 0)) #? {(c 1 3, (ub (c 1 3) pk (bk 5) (x3tt 1 0), TWO)) }_ 2 ^^ 11,
  bol (pi1 (pi2 (x5t 1 0))) #? {(c 0 4, (ub (c 0 4) pk (bk 6) (x3tt 1 0), TWO)) }_ 2 ^^ 12,
  bol
    (! ((pi2 (pi2 (x5t 1 0))) #? {(c 1 3, (ub (c 1 3) pk (bk 5) (x3tt 1 0), TWO)) }_ 2 ^^ 11)) &
    ! ((pi2 (pi2 (x5t 1 0))) #? {(c 0 4, (ub (c 0 4) pk (bk 6) (x3tt 1 0), TWO)) }_ 2 ^^ 12),
  bol (pi2 (pi2 (dec (pi2 (pi2 (x5t 1 0))) (ske 2)))) #? TWO,
  msg
    (shufl (c 1 3, ub (c 1 3) pk (bk 5) (x3tt 1 0)) (c 0 4, ub (c 0 4) pk (bk 6) (x3tt 1 0))
       (pi1 (dec (pi2 (pi2 (x5t 1 0))) (ske 2)), pi1 (pi2 (dec (pi2 (pi2 (x5t 1 0))) (ske 2))))),
  bol
    ((to (x6t 1 0)) #? A) &
    (dist (tau 1 (pi1 (x6t 1 0))) (tau 2 (pi1 (x6t 1 0))) (tau 3 (pi1 (x6t 1 0)))) &
    (dist (tau 1 (pi2 (x6t 1 0))) (tau 2 (pi2 (x6t 1 0))) (tau 3 (pi2 (x6t 1 0)))),
  bol (acc1 1 1 3 5) & (bcheck (c 1 3) (x6t 1 0)), msg {(label (c 1 3) (x6t 1 0), (kc (N 3), THREE)) }_ 2 ^^ 13,
  bol
    ((to (x7t 1 0)) #? B) &
    (dist (tau 1 (pi1 (x7t 1 0))) (tau 2 (pi1 (x7t 1 0))) (tau 3 (pi1 (x7t 1 0)))) &
    (dist (tau 1 (pi2 (x7t 1 0))) (tau 2 (pi2 (x7t 1 0))) (tau 3 (pi2 (x7t 1 0)))),
  bol (acc2 1 0 4 6) & (bcheck (c 0 4) (x7t 1 0)), msg {(label (c 1 4) (x7t 1 0), (kc (N 4), THREE)) }_ 2 ^^ 14,
  bol
    ((dist (dec (tau 1 (x8t 1 0)) (ske 2)) (dec (tau 2 (x8t 1 0)) (ske 2)) (dec (tau 3 (x8t 1 0)) (ske 2))) &
     (pchecks (x8t 1 0) THREE)) &
    ((isin (bk 3) (dec (tau 1 (x8t 1 0)) (ske 2), (dec (tau 2 (x8t 1 0)) (ske 2), dec (tau 3 (x8t 1 0)) (ske 2)))) &
     (isin (bk 4) (dec (tau 1 (x8t 1 0)) (ske 2), (dec (tau 2 (x8t 1 0)) (ske 2), dec (tau 3 (x8t 1 0)) (ske 2))))) or
    (! (isin (bk 3) (dec (tau 1 (x8t 1 0)) (ske 2), (dec (tau 2 (x8t 1 0)) (ske 2), dec (tau 3 (x8t 1 0)) (ske 2))))) or
    ! (isin (bk 4) (dec (tau 1 (x8t 1 0)) (ske 2), (dec (tau 2 (x8t 1 0)) (ske 2), dec (tau 3 (x8t 1 0)) (ske 2)))),
  msg
    (shufl (tau 1 (dec (tau 1 (x8t 1 0)) (ske 2)), tau 2 (dec (tau 1 (x8t 1 0)) (ske 2)))
       (tau 1 (dec (tau 2 (x8t 1 0)) (ske 2)), tau 2 (dec (tau 2 (x8t 1 0)) (ske 2)))
       (tau 1 (dec (tau 3 (x8t 1 0)) (ske 2)), tau 2 (dec (tau 3 (x8t 1 0)) (ske 2))))].

  
unfold dist.

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
