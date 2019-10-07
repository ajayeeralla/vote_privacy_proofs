(************************************************************************)
(* Copyright (c) 2017-2018, Ajay Kumar Eeralla <ae266@mail.missouri.edu>*)     
(************************************************************************)
 Require Export voting.
 (** proofs **)

Theorem frame4_ind: (phi5 0 1) ~ (phi5 1 0).
Proof. repeat unfold phi5, phi4, phi3, phi2, phi1, t1, t2, t3, t4. repeat unfold t4.
       simpl.
apply IFBRANCH_M5 with (ml1:= phi0) (ml2:=phi0).
simpl.       repeat unfold Avote.
apply IFBRANCH_M4 with (ml1:= phi0 ++ [bol (theta x1 A), msg (tr 0 0 3 5 7 9)]) (ml2:= phi0 ++ [ bol (theta x1 A), msg (tr 0 1 3 5 7 9)]).
simpl.  
apply IFBRANCH_M3 with (ml1:= phi0 ++[ bol (theta x1 A), msg (tr 0 0 3 5 7 9), bol (theta (x2t 0) B), msg (tr 1 1 4 6 8 10)])(ml2:= phi0 ++[
  bol (theta x1 A), msg (tr 0 1 3 5 7 9), bol (theta (x2t 1) B), msg (tr 1 0 4 6 8 10)]).
apply IFBRANCH_M3 with (ml1:= phi0 ++[bol (theta x1 A), msg (tr 0 0 3 5 7 9), bol (theta (x2t 0) B), msg (tr 1 1 4 6 8 10), bol (to (x3tt 0 1)) #? A ])(ml2:= phi0 ++[bol (theta x1 A), msg (tr 0 1 3 5 7 9), bol (theta (x2t 1) B), msg (tr 1 0 4 6 8 10), bol (to (x3tt 1 0)) #? A]).
 
apply IFBRANCH_M2 with (ml1:= phi0 ++[bol (theta x1 A), msg (tr 0 0 3 5 7 9), bol (theta (x2t 0) B), msg (tr 1 1 4 6 8 10), bol (to (x3tt 0 1)) #? A, bol (acc 0 3 5 (x3tt 0 1)), msg (e 0 3 5 (x3tt 0 1) TWO 11 2) ])(ml2:= phi0 ++[bol (theta x1 A), msg (tr 0 1 3 5 7 9), bol (theta (x2t 1) B), msg (tr 1 0 4 6 8 10), bol (to (x3tt 1 0)) #? A, bol (acc 1 3 5 (x3tt 1 0)), msg (e 1 3 5 (x3tt 1 0) TWO 11 2)]).
simpl.
 
apply IFBRANCH_M2 with (ml1:= phi0 ++[bol (theta x1 A), msg (tr 0 0 3 5 7 9), bol (theta (x2t 0) B), msg (tr 1 1 4 6 8 10), bol (to (x3tt 0 1)) #? A, bol (acc 0 3 5 (x3tt 0 1)), msg (e 0 3 5 (x3tt 0 1) TWO 11 2), bol (to (x4ttt 0 1)) #? B ])(ml2:= phi0 ++[bol (theta x1 A), msg (tr 0 1 3 5 7 9), bol (theta (x2t 1) B), msg (tr 1 0 4 6 8 10), bol (to (x3tt 1 0)) #? A, bol (acc 1 3 5 (x3tt 1 0)), msg (e 1 3 5 (x3tt 1 0) TWO 11 2), bol (to (x4ttt 1 0)) #? B]).
simpl.

repeat unfold t5.
simpl.
repeat unfold mchecks, strm.
apply IFBRANCH_M1 with (ml1:= [msg A, msg B, msg M, msg C1, msg C2, msg C3, msg ONE, msg TWO, msg THREE, msg (vk 0), msg (vk 1), 
   msg (pke 2), bol (theta x1 A), msg (tr 0 0 3 5 7 9), bol (theta (x2t 0) B), msg (tr 1 1 4 6 8 10), 
   bol (to (x3tt 0 1)) #? A, bol (acc 0 3 5 (x3tt 0 1)), msg (e 0 3 5 (x3tt 0 1) TWO 11 2), bol (to (x4ttt 0 1)) #? B,
   bol (acc 1 4 6 (x4ttt 0 1)), msg (e 1 4 6 (x4ttt 0 1) TWO 12 2)])(ml2:= [msg A, msg B, msg M, msg C1, msg C2, msg C3, msg ONE, msg TWO, msg THREE, msg (vk 0), msg (vk 1), msg (pke 2),
  bol (theta x1 A), msg (tr 0 1 3 5 7 9), bol (theta (x2t 1) B), msg (tr 1 0 4 6 8 10), bol (to (x3tt 1 0)) #? A,
  bol (acc 1 3 5 (x3tt 1 0)), msg (e 1 3 5 (x3tt 1 0) TWO 11 2), bol (to (x4ttt 1 0)) #? B, bol (acc 0 4 6 (x4ttt 1 0)),
  msg (e 0 4 6 (x4ttt 1 0) TWO 12 2)]).
simpl.
unfold p, d. repeat unfold e.





Theorem frame8_ind: (phi8 0 1) ~ (phi8 1 0).
 Proof. unfold phi8. simpl. repeat unfold t1, t2, t3, t4, t4s, t4ss, t47, t48. repeat unfold tr. repeat unfold Avote, Bvote.
        repeat unfold t5. repeat unfold strm. repeat unfold t61, t62, t61s, t62s, t61ss, t62ss, t71, t72, t71s, t72s. repeat unfold fintrm. repeat unfold strm.
        apply IFBRANCH_M8 with (ml1:= phi0) (ml2:= phi0); simpl.
        apply IFBRANCH_M7 with (ml1:= phi0 ++ [bol (theta x1 A), msg (vk 0, (b 0 3 5, s 0 3 5 7 9))]) (ml2:= (phi0++[ bol (theta x1 A), msg (vk 0, (b 1 3 5, s 1 3 5 7 9))])); simpl.  
        apply IFBRANCH_M6 with (ml1:= phi0 ++ [ bol (theta x1 A), msg (vk 0, (b 0 3 5, s 0 3 5 7 9)), bol (theta (x2t 0) B), msg (vk 1, (b 1 4 6, s 1 4 6 8 10))]) (ml2:= phi0++ [  bol (theta x1 A), msg (vk 0, (b 1 3 5, s 1 3 5 7 9)), bol (theta (x2t 1) B), msg (vk 1, (b 0 4 6, s 0 4 6 8 10))]); simpl.

    

        apply IFBRANCH_M6 with (ml1:= phi0 ++ [ bol (theta x1 A), msg (vk 0, (b 0 3 5, s 0 3 5 7 9)), bol (theta (x2t 0) B), msg (vk 1, (b 1 4 6, s 1 4 6 8 10)),  bol (to (x3tt 0 1)) #? A]) (ml2:= phi0++ [  bol (theta x1 A), msg (vk 0, (b 1 3 5, s 1 3 5 7 9)), bol (theta (x2t 1) B), msg (vk 1, (b 0 4 6, s 0 4 6 8 10)), bol (to (x3tt 1 0)) #? A]); simpl. 
        apply IFBRANCH_M5 with (ml1:= phi0 ++ [ bol (theta x1 A), msg (vk 0, (b 0 3 5, s 0 3 5 7 9)), bol (theta (x2t 0) B), msg (vk 1, (b 1 4 6, s 1 4 6 8 10)),  bol (to (x3tt 0 1)) #? A,  bol (acc 0 3 5 (x3tt 0 1)), msg (e 0 3 5 (x3tt 0 1) TWO 11 2)]) (ml2:= phi0++ [  bol (theta x1 A), msg (vk 0, (b 1 3 5, s 1 3 5 7 9)), bol (theta (x2t 1) B), msg (vk 1, (b 0 4 6, s 0 4 6 8 10)), bol (to (x3tt 1 0)) #? A, bol (acc 1 3 5 (x3tt 1 0)), msg (e 1 3 5 (x3tt 1 0) TWO 11 2)]); simpl.
 

        apply IFBRANCH_M5 with (ml1:= phi0 ++ [ bol (theta x1 A), msg (vk 0, (b 0 3 5, s 0 3 5 7 9)), bol (theta (x2t 0) B), msg (vk 1, (b 1 4 6, s 1 4 6 8 10)),  bol (to (x3tt 0 1)) #? A,  bol (acc 0 3 5 (x3tt 0 1)), msg (e 0 3 5 (x3tt 0 1) TWO 11 2), bol (to (x4ttt 0 1)) #? B]) (ml2:= phi0++ [  bol (theta x1 A), msg (vk 0, (b 1 3 5, s 1 3 5 7 9)), bol (theta (x2t 1) B), msg (vk 1, (b 0 4 6, s 0 4 6 8 10)), bol (to (x3tt 1 0)) #? A, bol (acc 1 3 5 (x3tt 1 0)), msg (e 1 3 5 (x3tt 1 0) TWO 11 2), bol (to (x4ttt 1 0)) #? B]); simpl.
 
        apply IFBRANCH_M4 with (ml1:= phi0 ++ [ bol (theta x1 A), msg (vk 0, (b 0 3 5, s 0 3 5 7 9)), bol (theta (x2t 0) B), msg (vk 1, (b 1 4 6, s 1 4 6 8 10)),  bol (to (x3tt 0 1)) #? A,  bol (acc 0 3 5 (x3tt 0 1)), msg (e 0 3 5 (x3tt 0 1) TWO 11 2), bol (to (x4ttt 0 1)) #? B,  bol (acc 1 4 6 (x4ttt 0 1)), msg (e 1 4 6 (x4ttt 0 1) TWO 12 2)]) (ml2:= phi0++ [  bol (theta x1 A), msg (vk 0, (b 1 3 5, s 1 3 5 7 9)), bol (theta (x2t 1) B), msg (vk 1, (b 0 4 6, s 0 4 6 8 10)), bol (to (x3tt 1 0)) #? A, bol (acc 1 3 5 (x3tt 1 0)), msg (e 1 3 5 (x3tt 1 0) TWO 11 2), bol (to (x4ttt 1 0)) #? B,  bol (acc 0 4 6 (x4ttt 1 0)), msg (e 0 4 6 (x4ttt 1 0) TWO 12 2)]); simpl.

        
        apply IFBRANCH_M3 with (ml1:= phi0 ++ [ bol (theta x1 A), msg (vk 0, (b 0 3 5, s 0 3 5 7 9)), bol (theta (x2t 0) B), msg (vk 1, (b 1 4 6, s 1 4 6 8 10)),  bol (to (x3tt 0 1)) #? A,  bol (acc 0 3 5 (x3tt 0 1)), msg (e 0 3 5 (x3tt 0 1) TWO 11 2), bol (to (x4ttt 0 1)) #? B,  bol (acc 1 4 6 (x4ttt 0 1)), msg (e 1 4 6 (x4ttt 0 1) TWO 12 2),  bol (mchecks x5t 0 1 TWO),
   msg (shufl (p 1 (x5t 0 1)) (p 2 (x5t 0 1)) (p 3 (x5t 0 1)))]) (ml2:= phi0++ [  bol (theta x1 A), msg (vk 0, (b 1 3 5, s 1 3 5 7 9)), bol (theta (x2t 1) B), msg (vk 1, (b 0 4 6, s 0 4 6 8 10)), bol (to (x3tt 1 0)) #? A, bol (acc 1 3 5 (x3tt 1 0)), msg (e 1 3 5 (x3tt 1 0) TWO 11 2), bol (to (x4ttt 1 0)) #? B,  bol (acc 0 4 6 (x4ttt 1 0)), msg (e 0 4 6 (x4ttt 1 0) TWO 12 2), bol (mchecks x5t 1 0 TWO),
                                                                                  msg (shufl (p 1 (x5t 1 0)) (p 2 (x5t 1 0)) (p 3 (x5t 1 0)))]); simpl. 

           apply IFBRANCH_M3 with (ml1:= phi0 ++ [ bol (theta x1 A), msg (vk 0, (b 0 3 5, s 0 3 5 7 9)), bol (theta (x2t 0) B), msg (vk 1, (b 1 4 6, s 1 4 6 8 10)),  bol (to (x3tt 0 1)) #? A,  bol (acc 0 3 5 (x3tt 0 1)), msg (e 0 3 5 (x3tt 0 1) TWO 11 2), bol (to (x4ttt 0 1)) #? B,  bol (acc 1 4 6 (x4ttt 0 1)), msg (e 1 4 6 (x4ttt 0 1) TWO 12 2),  bol (mchecks x5t 0 1 TWO),
   msg (shufl (p 1 (x5t 0 1)) (p 2 (x5t 0 1)) (p 3 (x5t 0 1))),  bol (theta21 x6t A 0 1)]) (ml2:= phi0++ [  bol (theta x1 A), msg (vk 0, (b 1 3 5, s 1 3 5 7 9)), bol (theta (x2t 1) B), msg (vk 1, (b 0 4 6, s 0 4 6 8 10)), bol (to (x3tt 1 0)) #? A, bol (acc 1 3 5 (x3tt 1 0)), msg (e 1 3 5 (x3tt 1 0) TWO 11 2), bol (to (x4ttt 1 0)) #? B,  bol (acc 0 4 6 (x4ttt 1 0)), msg (e 0 4 6 (x4ttt 1 0) TWO 12 2), bol (mchecks x5t 1 0 TWO),
                                                                                                            msg (shufl (p 1 (x5t 1 0)) (p 2 (x5t 1 0)) (p 3 (x5t 1 0))), bol (theta21 x6t A 1 0)]); simpl.
           
 
            apply IFBRANCH_M2 with (ml1:= phi0 ++ [bol (theta x1 A), msg (vk 0, (b 0 3 5, s 0 3 5 7 9)), bol (theta (x2t 0) B), msg (vk 1, (b 1 4 6, s 1 4 6 8 10)),  bol (to (x3tt 0 1)) #? A,  bol (acc 0 3 5 (x3tt 0 1)), msg (e 0 3 5 (x3tt 0 1) TWO 11 2), bol (to (x4ttt 0 1)) #? B,  bol (acc 1 4 6 (x4ttt 0 1)), msg (e 1 4 6 (x4ttt 0 1) TWO 12 2),  bol (mchecks x5t 0 1 TWO),
   msg (shufl (p 1 (x5t 0 1)) (p 2 (x5t 0 1)) (p 3 (x5t 0 1))),  bol (theta21 x6t A 0 1),  bol (acc1 0 1 3 5) & (bcheck (c 0 3) (x6t 0 1)), msg (e1 0 3 x6t 1 13)]) (ml2:= phi0++ [bol (theta x1 A), msg (vk 0, (b 1 3 5, s 1 3 5 7 9)), bol (theta (x2t 1) B), msg (vk 1, (b 0 4 6, s 0 4 6 8 10)), bol (to (x3tt 1 0)) #? A, bol (acc 1 3 5 (x3tt 1 0)), msg (e 1 3 5 (x3tt 1 0) TWO 11 2), bol (to (x4ttt 1 0)) #? B,  bol (acc 0 4 6 (x4ttt 1 0)), msg (e 0 4 6 (x4ttt 1 0) TWO 12 2), bol (mchecks x5t 1 0 TWO),
                                                                                  msg (shufl (p 1 (x5t 1 0)) (p 2 (x5t 1 0)) (p 3 (x5t 1 0))), bol (theta21 x6t A 1 0), bol (acc1 1 0 3 5) & (bcheck (c 1 3) (x6t 1 0)), msg (e1 1 3 x6t 0 13)]); simpl.
 

                 apply IFBRANCH_M2 with (ml1:= phi0 ++ [bol (theta x1 A), msg (vk 0, (b 0 3 5, s 0 3 5 7 9)), bol (theta (x2t 0) B), msg (vk 1, (b 1 4 6, s 1 4 6 8 10)),  bol (to (x3tt 0 1)) #? A,  bol (acc 0 3 5 (x3tt 0 1)), msg (e 0 3 5 (x3tt 0 1) TWO 11 2), bol (to (x4ttt 0 1)) #? B,  bol (acc 1 4 6 (x4ttt 0 1)), msg (e 1 4 6 (x4ttt 0 1) TWO 12 2),  bol (mchecks x5t 0 1 TWO),
   msg (shufl (p 1 (x5t 0 1)) (p 2 (x5t 0 1)) (p 3 (x5t 0 1))),  bol (theta21 x6t A 0 1),  bol (acc1 0 1 3 5) & (bcheck (c 0 3) (x6t 0 1)), msg (e1 0 3 x6t 1 13),  bol (theta21 x7t B 0 1)]) (ml2:= phi0++ [bol (theta x1 A), msg (vk 0, (b 1 3 5, s 1 3 5 7 9)), bol (theta (x2t 1) B), msg (vk 1, (b 0 4 6, s 0 4 6 8 10)), bol (to (x3tt 1 0)) #? A, bol (acc 1 3 5 (x3tt 1 0)), msg (e 1 3 5 (x3tt 1 0) TWO 11 2), bol (to (x4ttt 1 0)) #? B,  bol (acc 0 4 6 (x4ttt 1 0)), msg (e 0 4 6 (x4ttt 1 0) TWO 12 2), bol (mchecks x5t 1 0 TWO),
                                                                                  msg (shufl (p 1 (x5t 1 0)) (p 2 (x5t 1 0)) (p 3 (x5t 1 0))), bol (theta21 x6t A 1 0), bol (acc1 1 0 3 5) & (bcheck (c 1 3) (x6t 1 0)), msg (e1 1 3 x6t 0 13), bol (theta21 x7t B 1 0)]); simpl.

           apply IFBRANCH_M1 with (ml1:= phi0 ++ [bol (theta x1 A), msg (vk 0, (b 0 3 5, s 0 3 5 7 9)), bol (theta (x2t 0) B), msg (vk 1, (b 1 4 6, s 1 4 6 8 10)),  bol (to (x3tt 0 1)) #? A,  bol (acc 0 3 5 (x3tt 0 1)), msg (e 0 3 5 (x3tt 0 1) TWO 11 2), bol (to (x4ttt 0 1)) #? B,  bol (acc 1 4 6 (x4ttt 0 1)), msg (e 1 4 6 (x4ttt 0 1) TWO 12 2),  bol (mchecks x5t 0 1 TWO),
   msg (shufl (p 1 (x5t 0 1)) (p 2 (x5t 0 1)) (p 3 (x5t 0 1))),  bol (theta21 x6t A 0 1),  bol (acc1 0 1 3 5) & (bcheck (c 0 3) (x6t 0 1)), msg (e1 0 3 x6t 1 13),  bol (theta21 x7t B 0 1), bol (acc1 0 1 4 6) & (bcheck (c 1 4) (x7t 0 1)), msg (e1 0 4 x7t 1 14)]) (ml2:= phi0++ [bol (theta x1 A), msg (vk 0, (b 1 3 5, s 1 3 5 7 9)), bol (theta (x2t 1) B), msg (vk 1, (b 0 4 6, s 0 4 6 8 10)), bol (to (x3tt 1 0)) #? A, bol (acc 1 3 5 (x3tt 1 0)), msg (e 1 3 5 (x3tt 1 0) TWO 11 2), bol (to (x4ttt 1 0)) #? B,  bol (acc 0 4 6 (x4ttt 1 0)), msg (e 0 4 6 (x4ttt 1 0) TWO 12 2), bol (mchecks x5t 1 0 TWO),
                                                                                                                                                                                                                                                                                     msg (shufl (p 1 (x5t 1 0)) (p 2 (x5t 1 0)) (p 3 (x5t 1 0))), bol (theta21 x6t A 1 0), bol (acc1 1 0 3 5) & (bcheck (c 1 3) (x6t 1 0)), msg (e1 1 3 x6t 0 13), bol (theta21 x7t B 1 0), bol (acc1 1 0 4 6) & (bcheck (c 0 4) (x7t 1 0)), msg (e1 1 4 x7t 0 14)]); simpl.


       unfold mchecks, theta21. unfold d.