Load "axioms".

(** * FOO Voting Prtocol *)
Section foo_prot.

(** * Ballot Privacy *)
(** Frame [phi10] represents initial knowledge pk, pk(V1), pk(V2), pk(A) *)

Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) .

Definition pii (n :nat) (t:message) := 
match n with
| 1 => pi1 t
| 2 => pi2 t
| _ => t
end. 

Fixpoint pil (l:list nat) (t:message):message:=
match l with
| nil => t
| cons h t' => (pii h (pil t' t))
end.

Eval compute in (pil [1;2;1] O).

Definition boltonum (b:bool): nat :=
match b with
| false => 0
| true => 1
end.

Fixpoint insatpos (n:nat) (t:message) (l:list message) :list message :=
match n with
| 0 => cons t l
| S n' => match l with
         | nil => (insatpos n' t (cons O l))
         | cons h t' => (cons h (insatpos n' t  t'))
         end
end.
          
Eval compute in (insatpos (boltonum false) (N 1) [O;O]).

Variable l: list message.
Variable b: bool.
Definition ind (b:bool):= (boltonum b).

(***************************************************************)

Definition phi10:= [msg (pkn 0); msg (pkn 1); msg (pkn 2); msg (pkn 3)].

(** Frame [phi11] *)

Definition mphi10 := (conv_mylist_listm phi10).
Definition x1 := (f mphi10). 
Definition qa00 := let b1:= (commit (pkn 0) (v 0) (r 4)) in 
                   let e1:= (blind b1 (r 5)) in
                   let b2:= (commit (pkn 0) (v 1) (r 4)) in 
                   let e2:= (blind b2 (r 5)) in
                   (if_then_else_M (EQ_M (to x1) (i 1)) ((pkn 1), (b1 , (sign (skn 1) e1))) 
                   	(if_then_else_M (EQ_M (to x1) (i 2)) ((pkn 2), (b2 , (sign (skn 2) e2))) O)).

Definition phi11 := phi10 ++ [msg qa00].

                          
(*
Definition phi11' := phi10 ++ [msg qa00].
Definition x2 := (f (conv_mylist_listm phi11')).

Definition qa00' := let b1:= (commit (pkn 0) (v 0) (r 4)) in
                    let b2:= (commit (pkn 0) (v 1) (r 4)) in 
                    let sb:= (unblind x2 (r 5)) in
                    (if_then_else_M (EQ_M (to x2) (i 1))& (ver (pkn 3) b1 x2) & (ver (pkn 3) b1 sb) (b1, sb)
                   			(if_then_else_M (EQ_M (to x2) (i 1))& (ver (pkn 3) b2 x2) & (ver (pkn 3) b2 sb) (b2, sb) O)).
                   
Definition phi11'' := phi11' ++ [msg qa00'].
Definition  x3:= (f (conv_mylist_listm phi11'')).
Definition qa0011 := (if_then_else_M (EQ_M (to x3) (i 1)) (r 5)
                                    (if_then_else_M (EQ_M (to x3) (i 2)) (r 7) O)). *)
  
(** Frame phi12 *)

Definition mphi11 := (conv_mylist_listm phi11).

Definition x2 := (f mphi11).
 
Definition qa10 := let b1:= (commit (pkn 0) (v 1) (r 6)) in 
                   let e1:= (blind b1 (r 7)) in    
                   let b2:= (commit (pkn 0) (v 0) (r 6)) in 
                   let e2:= (blind b2 (r 7)) in
    	           (if_then_else_M (EQ_M (to x2) (i 1)) ((pkn 1), (b1 , (sign (skn 1) e1))) 
                   	(if_then_else_M (EQ_M (to x2) (i 2)) ((pkn 2), (b2 , (sign (skn 2) e2))) O)).
 
Definition qa01 := let b1:= (commit (pkn 0) (v 0) (r 6)) in 
                   let e1:= (blind b1 (r 7)) in    
                   let b2:= (commit (pkn 0) (v 1) (r 6)) in 
                   let e2:= (blind b2 (r 7)) in
                   (if_then_else_M (EQ_M (to x2) (i 1)) ((pkn 1), (b1 , (sign (skn 1) e1))) 
                   	(if_then_else_M (EQ_M (to x2) (i 2)) ((pkn 2), (b2 , (sign (skn 2) e2))) 
                   		O)).

Definition t12 := (if_then_else_M (EQ_M (to x1) (i 1)) qa10
                  	(if_then_else_M (EQ_M (to x1) (i 2)) qa01
                  		O)).

Definition phi12 := phi11 ++ [msg t12].

 
(** Frame phi13 *) 

Definition mphi12 := (conv_mylist_listm phi12).

Definition x3 := (f mphi12).

Definition qa20 := let b2:= (commit (pkn 0) (v 0) (r 8)) in 
                   let e2:= (blind b2 (r 9)) in
                   (if_then_else_M (EQ_M (to x3) (i 2))  ((pkn 2), (b2 , (sign (skn 2) e2)))
                   	O).

Definition qa11 := let b1:= (commit (pkn 0) (v 1) (r 8)) in 
                   let e1:= (blind b1 (r 9)) in    
                   let b2:= (commit (pkn 0) (v 1) (r 8)) in 
                   let e2:= (blind b2 (r 9)) in
                   (if_then_else_M (EQ_M (to x3) (i 1)) ((pkn 1), (b1 , (sign (skn 1) e1))) 
                   	(if_then_else_M (EQ_M (to x3) (i 2))  ((pkn 2), (b2 , (sign (skn 2) e2))) 
                        	O)).

Definition qa02 := let b1:= (commit (pkn 0) (v 0) (r 8)) in 
                   let e1:= (blind b1 (r 9)) in
                   (if_then_else_M (EQ_M (to x3) (i 2))  ((pkn 1), (b1 , (sign (skn 1) e1)))
                   	O).

(****************************************************************************************)

Definition qa10_s := (if_then_else_M (EQ_M (to x2) (i 1)) qa20                                 
                     	(if_then_else_M (EQ_M (to x2) (i 2)) qa11
                        	O)).
                  
                   
Definition qa01_s := (if_then_else_M (EQ_M (to x2) (i 1)) qa11
                     	(if_then_else_M (EQ_M (to x2) (i 2)) qa02
                        	O)).
                   
Definition t13 := (if_then_else_M (EQ_M (to x1) (i 1)) qa10_s
                  	(if_then_else_M (EQ_M (to x1) (i 2)) qa01_s
                 		O)).
Definition phi13:= phi12 ++ [msg t13].

(** Frame phi14 *)

Definition mphi13 := (conv_mylist_listm phi13).

Definition x4 := (f mphi13).

Definition qa21 := let b2:= (commit (pkn 0) (v 0) (r 10)) in 
                   let e2:= (blind b2 (r 11)) in
                   (if_then_else_M (EQ_M (to x4) (i 2))  ((pkn 2), (b2 , (sign (skn 2) e2)))
                   	O).
Definition qa12 := let b1:= (commit (pkn 0) (v 1) (r 10)) in 
                   let e1:= (blind b1 (r 11)) in
                   (if_then_else_M (EQ_M (to x4) (i 1))  ((pkn 1), (b1 , (sign (skn 1) e1)))
                   	O).

(*******************************************************************************************)

Definition qa20_s := (if_then_else_M (EQ_M (to x3) (i 2))  qa21
                     	O).

Definition qa11_s := (if_then_else_M (EQ_M (to x3) (i 1)) qa21 
                   	(if_then_else_M (EQ_M (to x3) (i 2)) qa12 
                        	O)).

Definition qa02_s :=  (if_then_else_M (EQ_M (to x3) (i 2))  qa12 O).

(******************************************************************************************)

Definition qa10_ss := (if_then_else_M (EQ_M (to x2) (i 1)) qa20_s                                 
                      	(if_then_else_M (EQ_M (to x2) (i 2)) qa11_s
                        	O)).
                  
Definition qa01_ss := (if_then_else_M (EQ_M (to x2) (i 1)) qa11_s
                     	(if_then_else_M (EQ_M (to x2) (i 2)) qa02_s
                        	O)).
                   
Definition t14 := (if_then_else_M (EQ_M (to x1) (i 1)) qa10_ss
                  	(if_then_else_M (EQ_M (to x1) (i 2)) qa01_ss
                 		O)).
Definition phi14:= phi13 ++ [msg t14].

Goal phi14 ~ phi14.

(** Tactics to unfold various terms. *)
Ltac unf_phi := try unfold phi10, phi11, phi12, phi13, phi14.
Ltac unf_trm:=  try unfold  t12, t13,t14. 
Ltac unf_qa := try unfold  qa00, qa10, qa01; try unfold qa10_s, qa01_s; try unfold qa10_ss, qa01_ss;
	       try unfold qa10_ss, qa01_ss; try unfold qa20, qa02, qa11; try unfold qa20_s, qa02_s, qa11_s; try unfold qa12, qa21.
              

Ltac unf := try unf_phi; try unf_trm; try unf_qa .

repeat unf.
simpl.
End foo_prot.