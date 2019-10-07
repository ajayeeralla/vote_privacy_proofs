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