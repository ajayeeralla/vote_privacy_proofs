Require Export fooAxioms.
(** * Extending FreshInd *)
Open Scope msg_scope.
Notation "'[' x '<-' s ']' l" :=  (submsg_mylist x s l): msg_scope.
Axiom extFreshInd: forall {n} n1 n2 n3 (l:mylist n), (Fresh (cons n1 (cons n2 nil)) l) = true -> ((length (distMvars l))<=? 1)%nat = true ->
                                                  (distMvars l) = (cons n3 nil) ->
                                                  (submsg_mylist n3 (nonce n1) l) ~ (submsg_mylist n3 (nonce n2) l). (** ([ n3 <- (nonce n1)] l)%msg_scope ~ ([n3 <- (nonce n2)] l)%msg_scope.*)