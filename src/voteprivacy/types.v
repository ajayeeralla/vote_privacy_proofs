
(************************************************************************)
(* Copyright (c) 2017-2018, Ajay Kumar Eeralla <ae266@mail.missouri.edu>*)
(************************************************************************)
(** Mechanizing the proofs of Vote Privacy presented in the paper [Formal Analysis of Vote Privacy using Computationally Complete Symbolic Attacker] *)
(* Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality". *)

(** * Definitions *)

Require Export Coq.Arith.Arith.
Require Export Coq.Lists.List.
Require Export Coq.Arith.EqNat.
Require Export Coq.Arith.Plus.
Require Export Coq.Lists.List.
Require Export Coq.Lists.ListSet .
Require Export Coq.Init.Peano.
Require Export Coq.Structures.OrderedTypeEx.
Require Export Coq.Arith.Peano_dec.
Require Export Coq.Numbers.Natural.Peano.NPeano.
Require Export Coq.Init.Logic.
Require Export Coq.NArith.BinNat.
Require Export Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.SetoidTactics.
Require Export Setoid.
Require Export Program.
Require Export Coq.Logic.JMeq.


(** Mutually dependent inductive types: [Bool] and [message]
Note that type [Bool] is different from the built-in type [bool]
 *)
 (*Unset Elimination Schemes.*)

Set Boolean Equality Schemes.
Set Decidable Equality Schemes.

(** [ilist]: Polymorphic length-indexed list *)

Inductive ilist A : nat -> Type :=
| Nil : ilist A 0
| Cons: forall n, A-> ilist A n  -> ilist A (S n).


Inductive message: Type :=
(** Core symbols *)
| Mvar: nat -> message  (** Variable of type message *)
| O: message(** Empty message *)
| nonce: nat -> message(** Names *)
| ifm_then_else_: Bool -> message-> message-> message
| pair: message-> message-> message
| pi1: message-> message
| pi2: message-> message
| to: message -> message
| L: message-> message
| f: list message -> message(** Attacker's computation *)
(** FOO symbols *)
(** Phase numbers *)
| ONE: message
| TWO: message
| THREE: message
(** Agents *)
| A: message
| B: message
| M: message
(** Candidates (or Voters) *)
| C1: message
| C2: message
| C3: message
(** Vote values *)
| V0: message-> message
| V1: message-> message
(** Public Key *)
| pubkey: message-> message
(** Commitments *)
| kc: message-> message
| comm:  message-> message-> message
| open:  message-> message-> message-> message
(** Shuffling *)
| shufl: message-> message-> message-> message
(** Encryptions *)
| ke: message-> message
| re: message-> message
| enc: message-> message-> message-> message
| dec: message-> message-> message
(** Blind Signatures *)
| bot: message
| kb: message-> message
| rb: message-> message
| bsign: message-> message-> message-> message
| bl: message-> message-> message-> message
| ub: message-> message-> message-> message-> message
(** Signatures *)
| ks: message-> message
| rs: message-> message
| sign: message-> message-> message-> message
(** Zero symbol *)
| z: message -> message
(** Complement of a message *)
| compl: message -> message
with Bool : Type :=
(** Core symbols *)
| Bvar: nat -> Bool
| TRue: Bool
| FAlse: Bool
| eqb: Bool -> Bool -> Bool
| eqm: message-> message-> Bool
| ifb_then_else_:  Bool -> Bool -> Bool -> Bool
(** FOO symbols *)
(** Blind signatures *)
| acc : message-> message-> message-> message-> Bool
| bver : message-> message-> message-> Bool
(** Signatures *)
| ver : message-> message-> message-> Bool.

(** induction using using Schemes *)
Scheme message_Bool_ind := Induction for message Sort Prop
  with Bool_message_ind := Induction for Bool Sort Prop.

(* Print Bool_message_ind.
(*Eval compute in message_Bool_ind.*) *)

(** Mutual Induction *)
Combined Scheme message_Bool_mutind from message_Bool_ind, Bool_message_ind.

(* Print message_Bool_mutind. *)
(** Decide type equality *)
Lemma message_eq_dec : forall x y: message, { x = y} + {x <> y}
with Bool_eq_dec: forall b1 b2 : Bool, {b1 = b2} + {b1 <> b2}.
Proof. repeat  decide equality. repeat decide equality.
Qed.


(*Hint Resolve message_eq_dec.
Hint Resolve Bool_eq_dec.
Check message_Bool_ind.*)

Section All.
Variable A:Type.
Variable P: A -> Prop.
Fixpoint All_P (l:list A) : Prop :=
  match l with
    | nil => True
    | cons h t => P h /\ All_P t
  end.
End All.

(* Check All_P. *)

Section ind.
 Variable P: message -> Prop.
 Variable P0:Bool -> Prop.

 Hypothesis m_case: forall n, (P (Mvar n)).
 Hypothesis O_case: P O.

 Hypothesis f0 : forall n : nat, P (Mvar n).
 Hypothesis f1 : P O.
 Hypothesis f2 : forall n : nat, P (nonce n).
 Hypothesis f3 : forall b : Bool,
        P0 b -> forall m : message, P m -> forall m0 : message, P m0 -> P (ifm_then_else_ b m m0).
 Hypothesis f4 : forall m : message, P m -> forall m0 : message, P m0 -> P (pair m m0).
 Hypothesis f5 : forall m : message, P m -> P (pi1 m).
 Hypothesis f6 : forall m : message, P m -> P (pi2 m).
 Hypothesis f7 : forall m : message, P m -> P (to m).
 Hypothesis f8 : forall m : message, P m -> P (L m).
 Hypothesis f_case: forall (l : list message), (All_P message P l) -> P (f l).
 Hypothesis f9 : P ONE.
 Hypothesis f10 : P TWO.
 Hypothesis f11 : P THREE.
 Hypothesis f12 : P A.
 Hypothesis f13 : P B.
 Hypothesis f14 : P M.
 Hypothesis f15 : P C1.
 Hypothesis f16 : P C2.
 Hypothesis f17 : P C3.
 Hypothesis f18 : forall m : message, P m -> P (V0 m).
 Hypothesis f19 : forall m : message, P m -> P (V1 m).
 Hypothesis f20 : forall m : message, P m -> P (pubkey m).
 Hypothesis f21 : forall m : message, P m -> P (kc m).
 Hypothesis f22 : forall m : message, P m -> forall m0 : message, P m0 -> P (comm m m0).
 Hypothesis f23 : forall m : message, P m -> forall m0 : message, P m0 -> forall m1 : message, P m1 -> P (open m m0 m1).
 Hypothesis f24 : forall m : message, P m -> forall m0 : message, P m0 -> forall m1 : message, P m1 -> P (shufl m m0 m1).
 Hypothesis f25 : forall m : message, P m -> P (ke m).
 Hypothesis f26 : forall m : message, P m -> P (re m).
 Hypothesis f27 : forall m : message, P m -> forall m0 : message, P m0 -> forall m1 : message, P m1 -> P (enc m m0 m1).
 Hypothesis f28 : forall m : message, P m -> forall m0 : message, P m0 -> P (dec m m0).
 Hypothesis f29 : P bot.
 Hypothesis f30 : forall m : message, P m -> P (kb m).
 Hypothesis f31 : forall m : message, P m -> P (rb m).
 Hypothesis f32 : forall m : message, P m -> forall m0 : message, P m0 -> forall m1 : message, P m1 -> P (bsign m m0 m1).
 Hypothesis f33 : forall m : message, P m -> forall m0 : message, P m0 -> forall m1 : message, P m1 -> P (bl m m0 m1).
 Hypothesis f34 : forall m : message,
         P m ->
         forall m0 : message, P m0 -> forall m1 : message, P m1 -> forall m2 : message, P m2 -> P (ub m m0 m1 m2).
 Hypothesis f35 : forall m : message, P m -> P (ks m).
 Hypothesis f36 : forall m : message, P m -> P (rs m).
 Hypothesis f37 : forall m : message, P m -> forall m0 : message, P m0 -> forall m1 : message, P m1 -> P (sign m m0 m1).
 Hypothesis f38 : forall m : message, P m -> P (z m).
 Hypothesis f39 : forall n : nat, P0 (Bvar n).
 Hypothesis f40 : P0 TRue.
 Hypothesis f41 : P0 FAlse.
 Hypothesis f42 : forall b : Bool, P0 b -> forall b0 : Bool, P0 b0 -> P0 (eqb b b0).
 Hypothesis f43 : forall m : message, P m -> forall m0 : message, P m0 -> P0 (eqm m m0).
 Hypothesis f44 : forall b : Bool,
         P0 b -> forall b0 : Bool, P0 b0 -> forall b1 : Bool, P0 b1 -> P0 (ifb_then_else_ b b0 b1).
 Hypothesis f45 : forall m : message,
         P m ->
         forall m0 : message,
         P m0 -> forall m1 : message, P m1 -> forall m2 : message, P m2 -> P0 (acc m m0 m1 m2).
 Hypothesis f46 : forall m : message, P m -> forall m0 : message, P m0 -> forall m1 : message, P m1 -> P0 (bver m m0 m1).
 Hypothesis f47 : forall m : message, P m -> forall m0 : message, P m0 -> forall m1 : message, P m1 -> P0 (ver m m0 m1).
 Hypothesis f48: forall m: message, P m -> P (compl m).

Fixpoint message_Bool_ind' (t:message) : P t :=
   match t with
   | Mvar n => f0 n
   | O => f1
   | nonce n => f2 n
   | ifm_then_else_ b t1 t2 => (f3 b (Bool_message_ind' b) t1 (message_Bool_ind' t1) t2 (message_Bool_ind' t2))
   | pair t1 t2 =>  (f4 t1 (message_Bool_ind' t1) t2 (message_Bool_ind' t2))
   | pi1 t1 =>  (f5 t1 (message_Bool_ind' t1))
   | pi2 t1 => (f6 t1 (message_Bool_ind' t1))
   | to t1 => (f7 t1 (message_Bool_ind' t1))
   | L t1 => (f8 t1 (message_Bool_ind' t1))
   | f l => (f_case l ((fix list_ind (l : list message) : All_P message P l :=
          match l with
            | nil => I
            | h :: tl => conj (message_Bool_ind' h) (list_ind tl)
          end) l))
   | ONE => f9
   | TWO => f10
   | THREE => f11
   | A => f12
   | B => f13
   | M => f14
   | C1 => f15
   | C2 => f16
   | C3 => f17
   | V0 t1 => (f18 t1 (message_Bool_ind' t1))
   | V1 t1 => (f19 t1 (message_Bool_ind' t1))
   | pubkey t1 =>(f20 t1 (message_Bool_ind' t1))
   | kc t1 => (f21 t1 (message_Bool_ind' t1))
   | comm t1 t2 =>  (f22 t1 (message_Bool_ind' t1) t2 (message_Bool_ind' t2))
   | open t1 t2 t3 =>  (f23 t1 (message_Bool_ind' t1) t2 (message_Bool_ind' t2) t3 (message_Bool_ind' t3))
   | shufl t1 t2 t3 =>  (f24 t1 (message_Bool_ind' t1) t2 (message_Bool_ind' t2) t3 (message_Bool_ind' t3))
   | ke t1 => (f25 t1 (message_Bool_ind' t1))
   | re t1 =>  (f26 t1 (message_Bool_ind' t1))
   | enc t1 t2 t3 =>  (f27 t1 (message_Bool_ind' t1) t2 (message_Bool_ind' t2) t3 (message_Bool_ind' t3))
   | dec t1 t2 =>  (f28 t1 (message_Bool_ind' t1) t2 (message_Bool_ind' t2))
   | bot => f29
   | kb t1 => (f30 t1 (message_Bool_ind' t1))
   | rb t1 =>  (f31 t1 (message_Bool_ind' t1))
   | bsign t1 t2 t3 =>  (f32 t1 (message_Bool_ind' t1) t2 (message_Bool_ind' t2) t3 (message_Bool_ind' t3))
   | bl t1 t2 t3 =>  (f33 t1 (message_Bool_ind' t1) t2 (message_Bool_ind' t2) t3 (message_Bool_ind' t3))
   | ub t1 t2 t3 t4 =>  (f34 t1 (message_Bool_ind' t1) t2 (message_Bool_ind' t2) t3 (message_Bool_ind' t3) t4 (message_Bool_ind' t4))
   | ks t1 => (f35 t1 (message_Bool_ind' t1))
   | rs t1 =>  (f36 t1 (message_Bool_ind' t1))
   | sign t1 t2 t3 =>  (f37 t1 (message_Bool_ind' t1) t2 (message_Bool_ind' t2) t3 (message_Bool_ind' t3))
   | z t1 =>  (f38 t1 (message_Bool_ind' t1))
   | compl t1 => (f48 t1 (message_Bool_ind' t1))
   end
   with Bool_message_ind' (b:Bool) : P0 b :=
          match b with
          | (Bvar n) => f39 n
          | TRue => f40
          | FAlse => f41
          | (eqb b1 b2) => (f42 b1 (Bool_message_ind' b1) b2 (Bool_message_ind' b2))
          | (eqm m1 m2) => (f43 m1 (message_Bool_ind' m1) m2 (message_Bool_ind' m2))
          | ifb_then_else_ b t1 t2 => (f44 b (Bool_message_ind' b) t1 (Bool_message_ind' t1) t2 (Bool_message_ind' t2))
          | acc t1 t2 t3 t4 =>  (f45 t1 (message_Bool_ind' t1) t2 (message_Bool_ind' t2) t3 (message_Bool_ind' t3) t4 (message_Bool_ind' t4))
          | bver t1 t2 t3 =>  (f46 t1 (message_Bool_ind' t1) t2 (message_Bool_ind' t2) t3 (message_Bool_ind' t3))
          | ver t1 t2 t3 =>  (f47 t1 (message_Bool_ind' t1) t2 (message_Bool_ind' t2) t3 (message_Bool_ind' t3))
   end.
End ind.

Combined Scheme message_Bool_mut' from message_Bool_ind', Bool_message_ind'.

Declare Scope msg_scope.
Delimit Scope msg_scope with msg.

(** Notaions for [pair] *)
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z): msg_scope.

(* Eval compute in ( O, O ). *)
(* Eval compute in (O, O, O). *)
(* Check pair. *)
Definition triple {A:Type} (x y z: A) := (x, (y, z)).

(* Print Visibility. *)
(** Notation for [bot] *)
Notation "|_" := bot: msg_scope.

(* Eval compute in message_beq O O. *)

(** Eval compute in message_beq (f [(nonce 1); O]) (f [(nonce 1); (nonce 2)]) *)

(** [oursum] *)
Inductive oursum : Type :=
| msg :  message -> oursum
| bol:  Bool  -> oursum.

(** Notations for list message etc. *)
Notation Mlist := (list message).
Notation Blist := (list Bool).
Notation oslist := (list oursum).
Notation Nlist := (list nat).

(** decide oursum equality *)
Lemma oursum_eq_dec: forall x y : oursum, {x = y} + {x<> y}.
Proof. decide equality. apply message_eq_dec. apply Bool_eq_dec. Qed.

(** End tactics *)
(* Require Import List. *)

(** Notations *)
Notation "x : l" := (Cons _ _ x l) (at level 70) : msg_scope.
Notation "[]" := (Nil _) : msg_scope.
Notation "[ x ]" := (Cons _ _ x (Nil _)) : msg_scope.
Notation "[ x , .. , y ]" := (Cons _ _ x ..(Cons _ _ y (Nil _)) ..) : msg_scope.

(** bool equalities *)
(* Infix "=?" := message_beq: msg_scope. *)
Infix "?=" := Bool_beq : msg_scope.
Infix "=?=" := oursum_beq (at level 72) : msg_scope.

(** Decidable [ilist] equality *)

Open Scope msg_scope.
Delimit Scope msg_scope with msg.
Fixpoint ilist_beq {m1 m2} (l1 : ilist oursum m1)( l2: ilist oursum m2) :bool:=
match l1, l2 with
    | [], []  => true
    | Cons _ n' h1 t1 , Cons _ m' h2 t2 => if (beq_nat n' m') then  (andb (oursum_beq h1 h2) (ilist_beq t1 t2))
                                                                  else false
    | _ , _ => false
end.

(* Print Scope nat_scope. *)
(* Eval compute in 1<=?2. *)

Notation "'If' c1 'then' c2 'else' c3" := (ifm_then_else_ c1 c2 c3)
(at level 200, right associativity, format
                                      "'[v   ' 'If'  c1 '/' '[' 'then'  c2  ']' '/' '[' 'else'  c3 ']' ']'"): msg_scope.

Notation "'IF' c1 'then' c2 'else' c3" := (ifb_then_else_ c1 c2 c3)
(at level 200, right associativity, format
"'[v   ' 'IF'  c1 '/' '[' 'then'  c2  ']' '/' '[' 'else'  c3 ']' ']'"): msg_scope.


(** [mylist]: an [ilist] with type [oursum] *)
Definition mylist : nat-> Type := ilist oursum.

(** Decidable [mylist] equality *)
Fixpoint mylist_beq {m1 m2} (l1: mylist m1) ( l2:mylist m2) :bool:=
  match l1, l2 with
    | [] , [] => true
    | Cons _ n' h1 t1 , Cons _ m' h2 t2 => if (beq_nat n' m') then (andb (oursum_beq h1 h2) (mylist_beq t1 t2))
                                                                 else false
    | _ , _ => false
  end.


Infix "=?" := mylist_beq (at level 70): msg_scope.

(** Eval compute in ( [msg O , msg O] =? [msg O, msg (f (cons O nil)) ]) **)
(** Abbrevations *)
(** [notb] *)
Definition  notb (b: Bool) := (IF b then (FAlse) else (TRue)).
Notation "! x" := (notb x) (at level 0): msg_scope.

(** [andB] *)
Definition andB (b1 b2 :Bool) := IF b1 then b2 else FAlse.
Infix " & " := andB (at level 0, right associativity): msg_scope.

(** [orB] *)
Definition orB (b1 b2 : Bool) := IF b1 then TRue else b2.
Infix " 'or' " := orB (at level 0, right associativity): msg_scope.

Notation " '|' x '|' " := (L x) (at level 10, right associativity): msg_scope.
(* Eval compute in (enc O O O). *)

(** eqm *)
Infix " '#?' " := eqm (at level 0, right associativity): msg_scope.

(** [eql] *)

Definition eql m1 m2 := |m1|#?|m2|.

(** Public and Secret keys *)

(** * Encryptions *)

Definition pke (n:nat) := (pi1 (ke (nonce n))).
Definition ske (n:nat) := (pi2 (ke (nonce n))).
Definition er (n:nat) := (re (nonce n)).
Notation "'{' x '}_' n '^^' n' " := (enc x (pke n) (er n')) (at level 0, right associativity): msg_scope.

(* Eval compute in { O }_ 2 ^^ 3. *)
(** * Blind singatures *)
Definition pkb (n:nat) := (pi1 (kb (nonce n))).
Definition skb (n:nat) := (pi2 (kb (nonce n))).

(** * Digital Signatures *)
Definition vk (n:nat) := (pi1 (ks (nonce n))).
Definition ssk (n:nat) := (pi2 (ks (nonce n))).

(** Check if a term of oursum starts with [bol] constructor *)
Definition chkbol_os (a : oursum) : bool  :=
  match a with
  | bol b => true
  | msg m => false
  end.

(** Check if a term of [oursum] starts with [msg] constructor *)
Definition chkmsg_os (a : oursum) : bool  :=
  match a with
  | bol a' => false
  | msg a' => true
  end.

(** Get [Bool] term out of an [oursum] term *)
Definition ostobol (a :oursum) : Bool :=
  match a with
  | bol a' => a'
  | msg a' => TRue
  end.

(** Get [msg] term out of an [oursum] term *)
Definition ostomsg (a : oursum) : message :=
  match a with
  | bol a' => O
  | msg a' => a'
  end.
(* Open Scope msg_scope. *)
(* Eval  compute in [msg O, msg O]. *)

(** [ilist msg n] --> [mylist n] *)
(* Open Scope msg_scope. *)
Fixpoint conv_mlist_mylist {n:nat} (ml : ilist message n) : mylist n :=
  match ml with
  | []=> []
  | a : h => msg a : (conv_mlist_mylist h)
  end.

(** [ilist Bool n] --> [mylist n] *)
Fixpoint conv_blist_mylist {n:nat} (ml : ilist Bool n) : mylist n :=
  match ml with
  | [] => []
  | a : h => bol a : (conv_blist_mylist h)
  end.

(** [list msg] --> [mylist (length l)] *)
Fixpoint conv_listm_mylist ( l :  Mlist) : mylist (length l) :=
  match l with
  | nil => []
  | cons a h => msg a : (conv_listm_mylist h)
  end.

(** [mylist n] --> [list messge] *)
Fixpoint toListm {n:nat} (osl: mylist n) : Mlist :=
  match osl with
  | [] => nil
  | a : h => cons  (if (chkmsg_os a) then (ostomsg a) else O) (toListm h)
  end.

(** [mylist n] --> [oslist] *)
Fixpoint conv_mylist_listos {n:nat} (osl:mylist n) :oslist :=
  match osl with
  | [] => nil
  | a : h => (cons a (conv_mylist_listos h ) )
  end.

(** [mylist n] --> [ilist Bool n] *)
Fixpoint conv_mylist_listb {n:nat} (osl: mylist n) : ilist Bool n :=
  match osl with
  | [] => []
  | a : h => Cons _ _ (if (chkbol_os a) then (ostobol a) else TRue) (conv_mylist_listb h)
  end.

(** [oslist] --> [mylist (length l)] *)
Fixpoint conv_listos_mylist (l : oslist) : (mylist (length l)) :=
  match l with
  | nil => []
  | cons h t => h: (conv_listos_mylist t)
  end.

(** [Sublist] *)

Definition sublist {A:Type} (n m:nat) (l:list A) :=
  skipn n (firstn m l).

(** Substitution: x <- s in t, where x, s, and t are [Bool] or [msg] *)

Reserved Notation "'[[' x ':=' s ']]' t" (at level 0).
Reserved Notation "'{{' x ':=' s '}}' t" (at level 0).

Fixpoint submsg_bol (n : nat )(s:message) (b:Bool) : Bool :=
  match b with
    | eqb  b1 b2 =>  eqb  ([[n:= s]]b1) ([[n:= s]] b2)
    | eqm t1 t2 => eqm ( {{n:= s }} t1) ( {{ n:=s }} t2)
    | ifb_then_else_ t1 t2 t3 => ifb_then_else_  ([[n:=s]]t1) ([[n:=s]] t2) ([[n:=s]]t3)
    | ver t1 t2 t3 => ver ({{n:=s}}t1) ({{n:=s}}t2) ({{n:=s}}t3)
    | bver t1 t2 t3 => bver ({{n:=s}}t1) ({{n:=s}}t2) ({{n:=s}}t3)
    | acc t1 t2 t3 t4 => acc ({{n:=s}}t1) ({{n:=s}}t2) ({{n:=s}}t3) ({{n:=s}}t4)
    | _ => b
  end
    where "'[[' x ':=' s ']]' t" := (submsg_bol x s t)
with submsg_msg (n : nat )(s:message) (t:message) : message :=
  match t with
  (** Core syntax *)
  | Mvar n' => if (beq_nat n n') then s else t
  | O       => t
  | nonce n' => t
  | ifm_then_else_ b1 t1 t2 =>  ifm_then_else_ ([[n:=s]] b1) ({{n:= s }} t1) ({{ n:=s }} t2)
  | pair t1 t2  => pair ({{n:= s }} t1) ( {{ n:=s }} t2)
  | pi1 t1 => pi1 ({{n:= s }} t1)
  | pi2 t2 => pi2 ({{ n:=s }} t2)
  | to t2 => to ({{ n:=s }} t2)
  | L t1 => L ({{n:= s }} t1)
  | f l => (f (@map message message  (submsg_msg n s) l))
  (** FOO syntax *)
  (** Vote values *)
  | V0 t1 => V0 ({{n:= s }} t1)
  | V1 t1 => V1 ({{ n:=s }} t1)
  (** Public Key *)
  | pubkey t1 => pubkey ({{n:= s }} t1)
  (** Commitments *)
  | kc t1 => kc ({{n:= s }} t1)
  | comm t1 t2 => comm ({{n:= s }} t1) ({{ n:=s }} t2)
  | open t1 t2 t3 => open ({{n:= s }} t1) ({{ n:=s }} t2) ({{ n:=s }} t3)
  (** Shuffling *)
  | shufl t1 t2 t3 => shufl ({{n:= s }} t1) ({{ n:=s }} t2) ({{ n:=s }} t3)
  (** Encryptions *)
  | ke t1 => ke ({{n:= s }} t1)
  | re t1 => re ({{n:= s }} t1)
  | enc t1 t2 t3 => enc ({{n:= s}} t1) ({{ n:=s }} t2) ({{ n:=s }} t3)
  | dec t1 t2 => dec ({{n:= s }} t1) ({{ n:=s }} t2)
  (** Blind Signatures *)
  | kb t1 => kb ({{n:= s }} t1)
  | rb t1 => rb ({{n:= s }} t1)
  | bsign t1 t2 t3 => bsign ({{n:= s}} t1) ({{ n:=s}} t2) ({{n:=s}} t3)
  | bl t1 t2 t3 => bl ({{n:= s}} t1) ({{ n:=s}} t2) ({{n:=s}} t3)
  | ub t1 t2 t3 t4 => ub ({{n:= s}} t1) ({{ n:=s}} t2) ({{n:=s}} t3) ({{n:=s}} t4)
  (** Signatures *)
  | ks t1 => ks ({{n:= s }} t1)
  | rs t1 => rs ({{n:= s }} t1)
  | sign t1 t2 t3 => sign ({{n:= s}} t1) ({{ n:=s}} t2) ({{n:=s}} t3)
  (** zero symbol *)
  | z t1 => z ({{n:= s }} t1)
  | compl t1 => compl ({{n:=s}} t1)
  (** all other constrs *)
  | _ => t
  end
  where "'{{' x ':=' s '}}' t" := (submsg_msg x s t).

(** Substitution: x <- s in t, x is of type variable, t is of [oursum] *)
Definition submsg_os (n:nat)(s:message) (t:oursum):oursum :=
  match t with
  | msg t1 =>  msg ({{n := s}} t1)
  | bol b1 =>  bol ( [[n := s]] b1)
  end.

(** Substitution in [ilist message n'] *)
Fixpoint submsg_mlist {n':nat} (n:nat)(s:message)(l: ilist message n') : ilist message n' :=
  match l with
  | [] => []
  | h:t  =>  ({{n := s}} h) : (submsg_mlist n s t )
  end.
(*Eval compute in (submsg_msg 1 O  (f [ (Mvar 1) ; (nonce 2) ; (nonce 1)])). *)
(* Eval compute in  ( {{ 1 := O }} (nonce 1) ). *)


(** Substitutions for [Bool] variable in [Bool] and [msg] *)
Reserved Notation "'[' x ':=' s ']' t" (at level 0).
Reserved Notation "'(' x ':=' s ')' t" (at level 0).
Fixpoint subbol_bol (n : nat )(s:Bool) (b:Bool) : Bool :=
   match b with
    | eqb  b1 b2 =>  eqb  ([n:=s]b1) ([n:= s] b2)
    | eqm t1 t2 => eqm ( (n:= s ) t1) ( ( n:=s ) t2)
    | ifb_then_else_ t1 t2 t3 => IF ([n:=s]t1) then ([n:=s] t2) else ( [n:=s]t3)
    | ver t1 t2 t3 => ver ((n:=s)t1) ((n:=s)t2) ((n:=s)t3)
    | bver t1 t2 t3 => bver ((n:=s)t1) ((n:=s)t2) ((n:=s)t3)
    | acc t1 t2 t3 t4 =>  acc ((n:=s)t1) ((n:=s)t2) ((n:=s)t3) ((n:=s)t4)
    | Bvar n' => if (beq_nat n' n) then s else b
    | _ => b
  end
    where "'[' x ':=' s ']' t" := (subbol_bol x s t)
with subbol_msg (n : nat )(s:Bool) (t:message) : message :=
  match t with
       (** Core syntax *)
  | ifm_then_else_ b1 t1 t2 =>  If ([n:=s] b1) then ( (n:= s ) t1) else ( ( n:=s ) t2)
  | pair t1 t2  => pair ((n:= s ) t1) ( ( n:=s ) t2)
  | pi1 t1 => pi1 ((n:= s ) t1)
  | pi2 t2 => pi2 (( n:=s ) t2)
  | to t2 => to (( n:=s ) t2)
  | L t1 => L ((n:= s ) t1)
  | f l => (f (@map message message  (subbol_msg n s) l))
  (** FOO syntax *)
  (** Vote values *)
  | V0 t1 => V0 ((n:= s ) t1)
  | V1 t1 => V1 (( n:=s ) t1)
  (** Public Key *)
  | pubkey t1 => pubkey ((n:= s ) t1)
  (** Commitments *)
  | kc t1 => kc ((n:= s ) t1)
  | comm t1 t2 => comm ((n:= s ) t1) (( n:=s ) t2)
  | open t1 t2 t3 => open ((n:= s ) t1) (( n:=s ) t2) (( n:=s ) t3)
  (** Shuffling *)
  | shufl t1 t2 t3 => shufl ((n:= s ) t1) (( n:=s ) t2) (( n:=s ) t3)
  (** Encryptions *)
  | ke t1 => ke ((n:= s ) t1)
  | re t1 => re ((n:= s ) t1)
  | enc t1 t2 t3 => enc ((n:= s) t1) (( n:=s ) t2) (( n:=s ) t3)
  | dec t1 t2 => dec ((n:= s ) t1) (( n:=s ) t2)
  (** Blind Signatures *)
  | kb t1 => kb ((n:= s ) t1)
  | rb t1 => rb ((n:= s ) t1)
  | bsign t1 t2 t3 => bsign ((n:= s) t1) (( n:=s) t2) ((n:=s) t3)
  | bl t1 t2 t3 => bl ((n:= s) t1) (( n:=s) t2) ((n:=s) t3)
  | ub t1 t2 t3 t4 => ub ((n:= s) t1) (( n:=s) t2) ((n:=s) t3) ((n:=s) t4)
  (** Signatures *)
  | ks t1 => ks ((n:= s ) t1)
  | rs t1 => rs ((n:= s ) t1)
  | sign t1 t2 t3 => sign ((n:= s) t1) (( n:=s) t2) ((n:=s) t3)
  (** Zero symbol *)
  | z t1 => z t1
  | compl t1 => compl ((n:= s) t1)
  (** all other constrs *)
  | _ => t
  end
 where "'(' x ':=' s ')' t" := (subbol_msg x s t).

(** Substitution for [Bool] variable in a term of type [oursum] *)
Definition  subbol_os (n:nat)(s:Bool) (t:oursum):oursum :=
  match t with
    |msg t1 =>  msg ((n := s) t1)
    |bol b1 =>  bol ( [n := s] b1)
  end.

(** Testing properties on list elements*)
Fixpoint test_list {X:Type} (test: X -> bool) (l:list X): bool :=
  match l with
    | nil => true
    | cons h t => if (test h) then (test_list test t) else false
  end.

(** Check if a term is ground *)
Reserved Notation " '?^' x " (at level 0).
Reserved Notation " '^?' x " (at level 0).

Fixpoint closBol (b:Bool):bool:=
  match b with
    | Bvar n' =>  false
    | eqb b1 b2 =>  ( ?^ b1) && (?^ b2)
    | eqm t1 t2 =>  ( ^? t1) && (^? t2)
    | ifb_then_else_ b1 t1 t2 =>  (?^ b1)&& (?^ t1) && (?^ t2)
    | ver t1 t2 t3 => (^? t1) && (^? t2) && (^? t3)
    | bver t1 t2 t3 => (^? t1) && (^? t2) && (^? t3)
    | acc t1 t2 t3 t4 => (^? t1) && (^? t2) && (^? t3) && (^? t4)
    | _ => true
  end
where " '?^' x" := (closBol x)
with closMsg (t:message) : bool:=
 match t with
  (** Core syntax *)
  | Mvar n' => false
  | ifm_then_else_ b1 t1 t2 =>   (?^ b1) && (^? t1) && (^? t2)
  | pair t1 t2  =>  (^? t1) && (^? t2)
  | pi1 t1 => ^? t1
  | pi2 t2 => ^? t2
  | to t1 => ^? t1
  | L t1 => ^? t1
  | f l => (@forallb message closMsg l)
  (** FOO syntax *)
  (** Vote values *)
  | V0 t1 => ^? t1
  | V1 t1 => ^? t1
  (** Public Key *)
  | pubkey t1 => ^? t1
  (** Commitments *)
  | kc t1 => ^? t1
  | comm t1 t2 =>  (^? t1) && (^? t2)
  | open t1 t2 t3 => (^? t1) && (^? t2) && (^? t3)
  (** Shuffling *)
  | shufl t1 t2 t3 => (^? t1) && (^? t2) && (^? t3)
  (** Encryptions *)
  | ke t1 => ^? t1
  | re t1 => ^? t1
  | enc t1 t2 t3 => (^? t1) && (^? t2) && (^? t3)
  | dec t1 t2 =>   (^? t1) && (^? t2)
  (** Blind Signatures *)
  | kb t1 => ^? t1
  | rb t1 => ^? t1
  | bsign t1 t2 t3 => (^? t1) && (^? t2) && (^? t3)
  | bl t1 t2 t3 => (^? t1) && (^? t2) && (^? t3)
  | ub t1 t2 t3 t4 => (^? t1) && (^? t2) && (^? t3) && (^? t4)
  (** Signatures *)
  | ks t1 => ^? t1
  | rs t1 => ^? t1
  | sign t1 t2 t3 => (^? t1) && (^? t2)&& (^? t3)
  (** zero symbol *)
  | z t1 => ^? t1
  | compl t1 => ^? t1
  (** all other constrs *)
  | _ => true
 end
where " '^?' x" := (closMsg x).

(** Check if a term of type of [oursum] is closed *)
Definition closOs (t:oursum): bool :=
  match t with
    | msg t1 =>  ^? (t1)
    | bol b1 =>  ?^ (b1)
  end.

(** Check if every element of [msg] list is closed *)
Fixpoint closMlist (l: Mlist):bool:=
  match l with
    | nil => true
    | cons  h t => (^? h) && (closMlist t)
  end.


(** Check if every element of [Bool] list is closed *)
Fixpoint closBlist (l: Blist ):bool:=
  match l with
    | nil => true
    | cons h t => (?^ h) && (closBlist t)
  end.

(** Check if [mylist] is closed *)
Fixpoint closMylist {n:nat} (l: mylist n):bool :=
  match l with
    | [] => true
    | h : t =>  (closOs h) && (closMylist t)
  end.

(** Check if a variable occur in a term of type [msg] or [Bool] *)

(*
Fixpoint var_free_bol (n : nat )(t:Bool) : bool :=
  match t with
    | Bvar n' => if (beq_nat n' n) then true else false
    | eqb  b1 b2 =>  orb (var_free_bol n b1)  ( var_free_bol n b2)
    | eqm t1 t2 => orb (var_free_msg n t1) ( var_free_msg n t2)
    | ifb t1 t2 t3 => orb ( var_free_bol n t1)  (orb (var_free_bol n t2)(var_free_bol n t3) )
    | eql t1 t2 => orb ( var_free_msg n t1) ( var_free_msg n t2)
    | ver t1 t2 t3 => (orb  (orb (var_free_msg n t1) (var_free_msg n t2)) (var_free_msg n t3))
    | bver t1 t2 t3 => (orb  (orb (var_free_msg n t1) (var_free_msg n t2)) (var_free_msg n t3))
    | bacc t1 t2 t3 t4 => (orb (orb  (orb (var_free_msg n t1) (var_free_msg n t2)) (var_free_msg n t3)) (var_free_msg n t4))
    | _ => true
  end
with var_free_msg (n : nat )(t:message) : bool :=
  match t with
  | (Mvar n') => if (beq_nat n' n) then true else false
  | ifm_then_else_ b1 t1 t2 => orb (var_free_bol n b1) (orb ( var_free_msg n  t1)( var_free_msg n t2))
  | pair t1 t2  => (orb (var_free_msg n t1) (var_free_msg n t2))
  | pi1 t1 => var_free_msg n t1
  | pi2 t2 => var_free_msg n t2
  | L t1 => var_free_msg n t1
  | f l => (@forallb message (var_free_msg n) l)
  (** FOO syntax *)
  (** Vote values *)
  | V0 t1 => var_free_msg n t1
  | V1 t1 => var_free_msg n t1
  (** Public Key *)
  | pubkey t1 => var_free_msg n t1
  (** Commitments *)
  | kc t1 => var_free_msg n t1
  | comm t1 t2 => orb (var_free_msg n t1) (var_free_msg n t2)
  | open t1 t2 t3 => orb (orb (var_free_msg n t1) (var_free_msg n t2)) (var_free_msg n t3)
  (** Shuffling *)
  | shufl t1 t2 t3 => orb (orb (var_free_msg n t1) (var_free_msg n t2)) (var_free_msg n t3)
  (** Encryptions *)
  | ke t1 => var_free_msg n t1
  | re t1 => var_free_msg n t1
  | enc t1 t2 t3 => orb (orb (var_free_msg n t1) (var_free_msg n t2)) (var_free_msg n t3)
  | dec t1 t2 =>  orb (var_free_msg n t1) (var_free_msg n t2)
  (** Blind Signatures *)
  | kb t1 => var_free_msg n t1
  | rb t1 => var_free_msg n t1
  | bsign t1 t2 t3 => orb (orb (var_free_msg n t1) (var_free_msg n t2)) (var_free_msg n t3)
  | bl t1 t2 t3 => orb (orb (var_free_msg n t1) (var_free_msg n t2)) (var_free_msg n t3)
  | ub t1 t2 t3 t4 => orb (orb (orb (var_free_msg n t1) (var_free_msg n t2)) (var_free_msg n t3)) (var_free_msg n t4)
  | acc t1 t2 t3 t4 => orb (orb (orb (var_free_msg n t1) (var_free_msg n t2)) (var_free_msg n t3)) (var_free_msg n t4)
  (** Signatures *)
  | ks t1 => var_free_msg n t1
  | rs t1 => var_free_msg n t1
  | sign t1 t2 t3 => orb (orb (var_free_msg n t1) (var_free_msg n t2)) (var_free_msg n t3)
  (** all other constrs *)
  | _ => true
  end.

(** Check if a variable occur in a term of type [oursum] *)

Definition var_free_os (n:nat) (t:oursum) : bool :=
  match t with
    | msg t1 => (var_free_msg n t1)
    | bol b1 => (var_free_bol n b1)
  end.

(** Check if [mylist] contain a variable in one of the element *)

Fixpoint var_free_mylist (n:nat) {m} (l:mylist m) : bool :=
  match l with
    | [] => false
    | h : t => (orb (var_free_os n h) (var_free_mylist n t))
  end.
*)
(** Concatenation of two mylists *)

Fixpoint appMylist {n1} {n2}  (ml1 : mylist n1) (ml2 : mylist n2) : mylist (plus n1 n2) :=
  match ml1 in (ilist _ n1) return (ilist _ (n1 + n2)) with
    | [] => ml2
    | Cons _ n1 x ml3 => Cons _ _ x (appMylist ml3  ml2 )
  end.

Infix " ++ " := appMylist: msg_scope.

(** (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3) *)

(**Theorem app_assoc: forall (n n' n'' : nat) (l1 :mylist n) (l2: mylist n') (l3: mylist n'') (fr: (n + n')+ n'' = n + (n' + n'')),
                     l1 ++ (l2 ++ l3) = match fr in (_ = n''') return  mylist n''' with
                                          | eq_refl =>  (l1 ++ l2) ++ l3

                                        end.
Proof. induction l1. intros. pose proof( UIP_refl).  rewrite (UIP_refl _ _ fr).  simpl. reflexivity.
       intros. injection fr; intro fr'. simpl.
       rewrite (IHl1 l2 l3 fr').
generalize  ((l1 ++ l2) ++ l3).
generalize fr fr'. simpl.
pose proof(plus_assoc).
rewrite plus_assoc.
intros.
rewrite (UIP_refl _ _ fr0).
rewrite (UIP_refl _ _ fr'0).
 reflexivity.
Qed.

Hint Resolve app_assoc.
Check plus_n_O 1.
Check eq_sym (plus_n_O 1).
Definition eq_n_O (n:nat): (n + 0 = n) := eq_sym (plus_n_O n).
Lemma eq_n_O_O : forall (n:nat), (n + 0 + 0 = n).
Proof. intros.
replace (n + 0) with n.
apply eq_n_O.
apply (plus_n_O n).
Show Proof.
Check eq_ind.
Qed.
Definition iapp { n m} (a: mylist n) (b:mylist m) : (mylist (n+m)) :=
   let c : mylist n :=
      match eq_sym (plus_n_O n) in (_ = n) return ilist _ n with
       | eq_refl => appMylist a []
      end in
           appMylist c b. *)

 (*
      Lemma myapp_l_nil : forall n (fr: n + 0 = n ) (l : mylist n),
           (match fr in (_ = n) return ilist _ n with
            | eq_refl =>  l ++ []
            end) = l .

      Proof.  induction l. simpl.  rewrite (UIP_refl _ _ fr).   reflexivity.
              injection fr. intros fr'. simpl. rewrite <-(IHl fr'). generalize (l ++ []). generalize fr fr'. simpl.
               rewrite <-fr'.
              simpl. intros. rewrite (UIP_refl _ _ fr'). injection H.  intro fr. simpl. rewrite IHl.
              generalize l. generalize (eq_n_O (S n)) (eq_n_O n). simpl.  intros.  simpl. rewrite (UIP_refl _ _ H0 ). rewrite  <- fr. intros.  rewrite fr in rewrite fr.
        destruct (eq_sym (plus_n_O 0)).  with (eq_refl 0)
       simpl.
       pose proof(iapp [] []). simpl.
       compute.
  Lemma mylist_app_involutive : forall { n} (l : mylist n),
      l = (match eq_n_O_O n in (_ = n) return ilist _ n with
           | eq_refl => (appMylist (appMylist l []) [])
          end).
Proof.
intros.
destruct l.
compute. Check eq_refl.
replace (eq_n_O_O 0) with (eq_refl 0).
reflexivity.  simpl.
replace (eq_n_O_O (S n)) with (eq_refl (S n)).
Check (eq_n_O_O 0).
Check (eq_refl 0).

compute.
reflexivity.

destruct (eq_n_O_O 0).
reflexivity.
 as [|(Nil A) |(Cons A m h t)].
destruct (eq_n_O_O n) as [|eq1].

Theorem app_nil : forall (n:nat) (l:mylist n) (fr : n+ 0 = n),
                    (l ++ []) = match fr in (_ = n') return mylist n' with
                                  |eq_refl=> l
                                end. *)
(** Check If a name n occurs  *)

Fixpoint occur_name_bol (n : nat )(t:Bool) : bool :=
  match t with
    | eqb  b1 b2 =>  (occur_name_bol n b1) ||  (occur_name_bol n b2)
    | eqm t1 t2 => (occur_name_msg n t1) || (occur_name_msg n t2)
    | ifb_then_else_ t1 t2 t3 => (occur_name_bol n t1) || (occur_name_bol n t2) || (occur_name_bol n t3)
    | ver t1 t2 t3 => (occur_name_msg n t1) || (occur_name_msg n t2) || (occur_name_msg n t3)
    | bver t1 t2 t3 => (occur_name_msg n t1) || (occur_name_msg n t2) || (occur_name_msg n t3)
    | acc t1 t2 t3 t4 => (occur_name_msg n t1) || (occur_name_msg n t2) || (occur_name_msg n t3) || (occur_name_msg n t4)
    | _ => false
  end
with occur_name_msg (n : nat )(t:message) : bool :=
  match t with
  | ifm_then_else_ b3 t1 t2 => (occur_name_bol n b3) || (occur_name_msg n  t1) || (occur_name_msg n t2)
  | nonce n'=> if (beq_nat n' n) then true else false
  | pair t1 t2 => (occur_name_msg n t1) || (occur_name_msg n t2)
  | pi1 t1 => (occur_name_msg n t1)
  | pi2 t1 => (occur_name_msg n t1)
  | L t1 => (occur_name_msg n t1)
  | f l => (@existsb message (occur_name_msg n) l)
  (** FOO syntax *)
  (** Vote values *)
  | V0 t1 => false
  | V1 t1 => false
  (** Public Key *)
  | pubkey t1 => false
  (** Commitments *)
  | kc t1 => occur_name_msg n t1
  | comm t1 t2 =>  (occur_name_msg n t1) || (occur_name_msg n t2)
  | open t1 t2 t3 =>   (occur_name_msg n t1) || (occur_name_msg n t2) || (occur_name_msg n t3)
  (** Shuffling *)
  | shufl t1 t2 t3 =>   (occur_name_msg n t1) || (occur_name_msg n t2) || (occur_name_msg n t3)
  (** Encryptions *)
  | ke t1 => occur_name_msg n t1
  | re t1 => occur_name_msg n t1
  | enc t1 t2 t3 =>   (occur_name_msg n t1) || (occur_name_msg n t2) || (occur_name_msg n t3)
  | dec t1 t2 =>   (occur_name_msg n t1) || (occur_name_msg n t2)
  (** Blind Signatures *)
  | kb t1 => occur_name_msg n t1
  | rb t1 => occur_name_msg n t1
  | bsign t1 t2 t3 =>   (occur_name_msg n t1) || (occur_name_msg n t2) || (occur_name_msg n t3)
  | bl t1 t2 t3 =>   (occur_name_msg n t1) || (occur_name_msg n t2) || (occur_name_msg n t3)
  | ub t1 t2 t3 t4 =>    (occur_name_msg n t1) || (occur_name_msg n t2) || (occur_name_msg n t3) || (occur_name_msg n t4)
  (** Signatures *)
  | ks t1 => occur_name_msg n t1
  | rs t1 => occur_name_msg n t1
  | sign t1 t2 t3 =>  (occur_name_msg n t1) || (occur_name_msg n t2) || (occur_name_msg n t3)
  (** zero symbol *)
  | z t1 => false
  | compl t1 => occur_name_msg n t1
  (** all other constrs *)
  | _ => false
  end.


(** Check if absence of a variable in a term of [oursum] *)
Definition  occurOs (n:nat)(t:oursum): bool :=
  match t with
  | bol b1 => occur_name_bol n b1
  | msg t => occur_name_msg n t
  end.

(** Check if absence of a variable in [ilist] *)
Fixpoint occurMlist (n:nat) (ml : Mlist):bool :=
  match ml with
    | nil => false
    | h:: ml1 => (occur_name_msg n h) || (occurMlist n ml1)
  end.

(** Check if absence of a variable in [ilist] *)
Fixpoint occurBlist (x:nat) (ml : Blist):bool :=
  match ml with
    | nil => false
    | h :: ml1 =>  (occur_name_bol x h) || (occurBlist x ml1)
  end.

(** Check if absence of a variable in [mylist] *)
Fixpoint occur_name_mylist {m:nat}(x:nat) (ml :  mylist m):bool :=
  match ml with
    | [] => false
    | h : ml1 =>  (occurOs x h) || (occur_name_mylist x ml1)
  end.

(** Number of occurences of an element in [ilist] *)
Fixpoint count_occur  (x : nat)(l : Nlist) : nat :=
  match l with
    | nil => 0
    | y::t =>  if (beq_nat y x) then S (count_occur x t) else (count_occur x t)
  end.

(** Check if no redundancies in [ilist] *)
(* Check beq_nat. *)
Fixpoint dupNlist (l:Nlist): bool :=
  match l with
    | nil => false
    | h :: t => let x := (count_occur h l) in
              match (1<?x) with
                | true => true
                | false => dupNlist t
              end
  end.

(** Eval compute in (dupNlist [1;1]).*)
(** Eval compute in (dupNlist [1;2;3]) *)

Definition noDupNlist l := negb (dupNlist l).

(* Compute [1]%list. *)
(** Check if each element in [ilist nat n] occurs in [ilist msg m] *)
(*
Fixpoint occNlistMlist {n:nat} (nl:ilist nat n){m}(ml:ilist message m): bool :=
  match nl with
    | [] => true
    | h:t=>  (occur_mlist h ml) (notocclist_mlist t ml))
  end.

(*Eval compute in (occur_mlist 1 [(nonce 2),(nonce 4)]). *)
(*Eval compute in True \/ False. *)
*)
(** Check if each element in (ilist nat n) occurs in (mylist m) *)
Fixpoint occurNlistMylist {m:nat}(nl:Nlist)(ml: mylist m): bool :=
match nl with
|nil => false
| h::t=> (occur_name_mylist h ml) || (occurNlistMylist t ml)
end.
(*Eval compute in (occurNlistMylist (cons 1 nil) [msg (nonce 2), msg (nonce 4)]). *)


(** Check if an element occurs in [ilist] *)
(*
 Fixpoint occur_nlist {n:nat}(a:nat) (l:ilist nat n) : bool :=
    match l with
      | [] => false
      | h:t =>   if (beq_nat h a) then false else  true || (occur_nlist a t)
    end.
(*Eval compute in (occur_nlist 1 [2,3]). *)
(*Eval compute in (S (pred 1)).*) *)

(** Function [Fresh] to check if the list of numbers are freshly generated numbers *)
Definition Fresh {m:nat} (nl : Nlist)(ml : mylist m): bool := (noDupNlist nl) && (negb (occurNlistMylist nl ml)).
(*Eval compute in noDupNlist (cons 1 nil). *)
  (* Eval compute in Fresh (cons 1 nil) [msg (comm (V0 (nonce 1)) (kc (nonce 7)))]. *)
(** Check if an [exp term (exp (G n) (g n) (r n1))] occurs in a term *)
(** Check if a term t of type msg occurs in a term of either [msg] or [Bool] type *)
Fixpoint checkmtbol (t:message) (b:Bool) : bool :=
  match b with
    | eqb  b1 b2 => orb (checkmtbol t b1)  (checkmtbol t b2)
    | eqm t1 t2 => orb (checkmtmsg t t1) (checkmtmsg t t2)
    | ifb_then_else_ t1 t2 t3 => orb ( checkmtbol t t1)  (orb (checkmtbol t t2)(checkmtbol t t3) )
    | ver t1 t2 t3 => (orb  (orb (checkmtmsg t t1) (checkmtmsg t t2)) (checkmtmsg t t3))
    | bver t1 t2 t3 => (orb  (orb (checkmtmsg t t1) (checkmtmsg t t2)) (checkmtmsg t t3))
    | acc t1 t2 t3 t4 =>(orb (orb  (orb (checkmtmsg t t1) (checkmtmsg t t2)) (checkmtmsg t t3)) (checkmtmsg t t4))
    | _ => false
  end
with checkmtmsg (t:message) (t':message) : bool :=
       if (message_beq t t') then true else
         match t' with
           | ifm_then_else_ b3 t1 t2 => orb (checkmtbol t b3) (orb ( checkmtmsg t  t1)( checkmtmsg t t2))
           | pair t1 t2 => orb( checkmtmsg t t1) ( checkmtmsg t t2)
           | pi1 t1 => ( checkmtmsg t t1)
           | pi2 t1 => ( checkmtmsg t t1)
           | L t1 => (checkmtmsg t t1)
           | f l => (@existsb message (checkmtmsg t) l)
           (** foo function symbol *)
           (** FOO syntax *)
           (** Vote values *)
           | V0 t1 => checkmtmsg t t1
           | V1 t1 => checkmtmsg t t1
           (** Public Key *)
           | pubkey t1 => checkmtmsg t t1
           (** Commitments *)
           | kc t1 => checkmtmsg t t1
           | comm t1 t2 => orb (checkmtmsg t t1) (checkmtmsg t t2)
           | open t1 t2 t3 => orb (orb (checkmtmsg t t1) (checkmtmsg t t2)) (checkmtmsg t t3)
           (** Shuffling *)
           | shufl t1 t2 t3 => orb (orb (checkmtmsg t t1) (checkmtmsg t t2)) (checkmtmsg t t3)
           (** Encryptions *)
           | ke t1 => checkmtmsg t t1
           | re t1 => checkmtmsg t t1
           | enc t1 t2 t3 => orb (orb (checkmtmsg t t1) (checkmtmsg t t2)) (checkmtmsg t t3)
           | dec t1 t2 =>  orb (checkmtmsg t t1) (checkmtmsg t t2)
           (** Blind Signatures *)
           | kb t1 => checkmtmsg t t1
           | rb t1 => checkmtmsg t t1
           | bsign t1 t2 t3 => orb (orb (checkmtmsg t t1) (checkmtmsg t t2)) (checkmtmsg t t3)
           | bl t1 t2 t3 => orb (orb (checkmtmsg t t1) (checkmtmsg t t2)) (checkmtmsg t t3)
           | ub t1 t2 t3 t4 => orb (orb (orb (checkmtmsg t t1) (checkmtmsg t t2)) (checkmtmsg t t3)) (checkmtmsg t t4)
           (** Signatures *)
           | ks t1 => checkmtmsg t t1
           | rs t1 => checkmtmsg t t1
           | sign t1 t2 t3 => orb (orb (checkmtmsg t t1) (checkmtmsg t t2)) (checkmtmsg t t3)
           (** all other constrs *)
           | z t1 => false
           | compl t1 => checkmtmsg t t1
           | _ => true
         end.

(** Check for given term [(exp (G n) (g n) (r n1))] occurs in [oursum] *)
(** Check if a msg term occurs in a term of [oursum] *)
Definition checkmtos (t:message) (t':oursum): bool :=
  match t' with
    |bol b1 => checkmtbol t b1
    |msg t'' => checkmtmsg t t''
  end.

(** Check for [exp] term in a term of type [list msg] *)
Fixpoint checkmtlism (t:message) (l: Mlist):bool :=
  match l with
    | nil => false
    |  cons h t' => (orb (checkmtmsg t h) (checkmtlism t t'))
  end.

(** Check for [exp] term in a term of type [mylist] *)
Fixpoint checkmtmylis (t:message) {m} (l: mylist m):bool :=
  match l with
    | [] => false
    |  h:t' => (orb (checkmtos t h) (checkmtmylis t t'))
  end.

(** Get an element at a [pos] in [mylist] *)
Fixpoint getelt_at_pos (p :nat) {m}   (ml : mylist m ) : oursum :=
  match (leb p m), p with
    | false, _  => msg O
    | true, 0 => msg O
    | true, 1  => match ml with
                    | [] => msg O
                    | h : t => h
                  end
    | true,  (S n') => match ml with
                         | [] => (msg O)
                         | h : t => (getelt_at_pos n' t)
                       end
  end.

(** Get an element at a [pos] in [ilist] *)
Fixpoint getelt_ml {m}  (p :nat) (ml : ilist message m) : message :=
  match p with
    | 0 => O
    | 1 => match ml with
             | [] => O
             | h : t => h
           end
    | (S n') => match ml with
                  | [] => O
                  | h : t => (getelt_ml   n' t)
                end
  end.

(** Appending an element to [mylist] at front *)
Definition app_elt_front (x:oursum) {n} (ml: mylist n) : mylist ( S n):=
  match ml with
    | [] => [x]
    | ml3 => (appMylist [x] ml3)
  end.
Notation " x +++ m1 " := (app_elt_front x m1)(at level 0, right associativity).
(*Eval compute in getelt_at_pos  2 [bol (Bvar 1) , bol (Bvar 2), msg (nonce 1), msg (nonce 2), msg (nonce 3)]. *)


(** Appending an element of [mylist] at rear *)
Fixpoint app_elt_last (x:oursum) {n} (ml: mylist n) : mylist ( S n):=
  match ml with
    | [] => [x]
    | h:ml3 => h : (app_elt_last x ml3)
  end.

(** Reversing [mylist] *)
Fixpoint reverse {n}(ml: mylist n) : mylist n :=
  match ml with
    | [] => []
    | x : ml' => (app_elt_last x (reverse ml') )
  end.

(** Insert an element at given position *)
Fixpoint insert_at_pos (p:nat) (x:oursum) {n} (l:mylist n) : mylist (S n) :=
  match (leb p n) , p with
    | false, _ => (app_elt_last (msg O) l)
    | true, 0  =>  (app_elt_last (msg O) l)
    | true, 1 => (app_elt_front x l)
    | true , (S n') => match l with
                         | [] => [x]
                         | h : t => (appMylist [h] (insert_at_pos n' x t))
                       end
  end.

(*Eval compute in (insert_at_pos 5 (msg O) [msg O,  msg O]). *)

(** Check if the term at [pos] is [Bool] *)
Definition chkbol_at_pos  {m} (n :nat) (ml :mylist m) : bool := (chkbol_os (getelt_at_pos  n ml)).

(** Check if the term at [pos] is [msg] *)
Definition chkmsg_at_pos {m} (n :nat) (ml :mylist m) : bool := (chkmsg_os (getelt_at_pos n ml)).

(** Negating an element at given [pos] in [mylist] *)
Definition neg_at_pos {m}   (p:nat ) (ml : mylist m) : mylist 1 :=
match  (chkbol_os (getelt_at_pos p ml)) with
| true => [bol (notb (ostobol (getelt_at_pos p ml)))]
| false =>  [(getelt_at_pos p ml)]
end .

(*Eval compute in neg_at_pos  2  [bol (Bvar 1) , bol (Bvar 2), msg (nonce 1), msg (nonce 2), msg (nonce 3)]. *)

(** Pairing two elements from [mylist] *)
Definition pair_at_pos {m}  (p1 p2 : nat) (ml : mylist m) : message :=
  match (chkmsg_os (getelt_at_pos  p1 ml)) with
    | true => match (chkmsg_os (getelt_at_pos  p2 ml)) with
                | true => (pair (ostomsg (getelt_at_pos  p1 ml)) (ostomsg (getelt_at_pos  p2 ml)))
                | false => (pair (ostomsg  (getelt_at_pos  p1 ml)) O)
              end
    | false => match (chkmsg_os (getelt_at_pos  p2 ml)) with
                 | true => (pair O (ostomsg (getelt_at_pos  p2 ml)))
                 | false => (pair O O)
               end
  end.

(** Constructing a [eqm] term in with the elements in [mylist] *)
Definition eqm_at_pos {m}  (p1 p2 : nat) (ml : mylist m) : Bool :=
  match (chkmsg_os (getelt_at_pos  p1 ml)) with
    | true => match (chkmsg_os (getelt_at_pos  p2 ml)) with
                | true => (eqm (ostomsg (getelt_at_pos  p1 ml)) (ostomsg (getelt_at_pos  p2 ml)))
                | false => (eqm (ostomsg (getelt_at_pos  p2 ml)) O)
              end
    | false => match (chkmsg_os (getelt_at_pos p2 ml)) with
                 | true => (eqm O (ostomsg (getelt_at_pos  p2 ml)))
                 | false => (eqm O O)
               end
  end.

(** Constructing a [eqb] term in with the elements in [mylist] *)
Definition eqb_at_pos {m}(p1 p2 : nat) (ml : mylist m) : Bool :=
  match (chkbol_os (getelt_at_pos  p1 ml)) with
    | true => match (chkbol_os (getelt_at_pos  p2 ml)) with
                | true => (eqb (ostobol (getelt_at_pos  p1 ml)) (ostobol (getelt_at_pos  p2 ml)))
                | false => (eqb (ostobol (getelt_at_pos  p1 ml)) TRue)
              end
    | false => match (chkbol_os (getelt_at_pos  p2 ml)) with
                 | true => (eqb TRue (ostobol (getelt_at_pos  p2 ml)))
                 | false => (eqb TRue TRue)
               end
  end.

(** Constructing a [andB] term in with the elements in [mylist] *)
Definition andB_at_pos {m} (p1 p2 : nat) (ml : mylist m) : Bool :=
  match (chkbol_os (getelt_at_pos  p1 ml)) with
    | true => match (chkbol_os (getelt_at_pos  p2 ml)) with
                | true => (andB (ostobol (getelt_at_pos  p1 ml)) (ostobol (getelt_at_pos  p2 ml)))
                | false => (andB (ostobol (getelt_at_pos  p1 ml)) TRue)
              end
    | false => match (chkbol_os (getelt_at_pos  p2 ml)) with
                 | true => (andB TRue (ostobol (getelt_at_pos  p2 ml)))
                 | false => (andB TRue TRue)
               end
  end.

(** Negating an element at [pos] in [mylist] *)
Definition notB_at_pos {m} (p : nat) (ml : mylist m) : Bool :=
  match (chkbol_os (getelt_at_pos  p ml)) with
    | true =>  notb (ostobol (getelt_at_pos  p ml))
    | false => notb (TRue)
  end.


(** Construction [ifm_then_else_] term from [mylist] *)
Definition IfM_at_pos {m}  (p1 p2 p3 p4 :nat)(ml : mylist m) : message :=
  match (chkbol_os (getelt_at_pos  p1 ml)) with
    | true => match (chkmsg_os (getelt_at_pos  p2 ml)) with
                | true => match (chkmsg_os (getelt_at_pos  p3 ml)) with
                            | true =>  (If (ostobol (getelt_at_pos  p1 ml)) then (ostomsg (getelt_at_pos  p2 ml)) else  ((ostomsg (getelt_at_pos  p3 ml))))
                            | false => (If (ostobol (getelt_at_pos  p1 ml)) then (ostomsg (getelt_at_pos  p2 ml)) else O)
                          end
                | false =>  match (chkmsg_os (getelt_at_pos  p3 ml)) with
                              | true =>  (If (ostobol (getelt_at_pos  p1 ml)) then O else ((ostomsg (getelt_at_pos  p3 ml))))
                              | false => (If (ostobol (getelt_at_pos  p1 ml)) then O else O)
                            end
              end
    | false =>  match (chkmsg_os (getelt_at_pos  p2 ml)) with
                  | true => match (chkmsg_os (getelt_at_pos  p3 ml)) with
                              | true =>  (If TRue then (ostomsg (getelt_at_pos  p2 ml)) else ((ostomsg (getelt_at_pos  p3 ml))))
                              | false => (If TRue then (ostomsg (getelt_at_pos  p2 ml)) else O)
                            end
                  | false =>  match (chkmsg_os (getelt_at_pos  p3 ml)) with
                                | true =>  (If TRue then O else ((ostomsg (getelt_at_pos  p3 ml))))
                                | false => (If TRue then O else  O)
                              end
                end

  end.

(** Construction [ifb] with terms in [mylist] *)
Definition IfB_at_pos {m}  (p1 p2 p3 p4 :nat)(ml : mylist m) : Bool :=
  match (chkbol_os (getelt_at_pos  p1 ml)) with
    | true => match (chkbol_os (getelt_at_pos  p2 ml)) with
                | true => match (chkbol_os (getelt_at_pos  p3 ml)) with
                            | true =>  (IF (ostobol (getelt_at_pos  p1 ml)) then (ostobol (getelt_at_pos  p2 ml)) else  ((ostobol (getelt_at_pos  p3 ml))))
                            | false => (IF (ostobol (getelt_at_pos  p1 ml)) then (ostobol (getelt_at_pos  p2 ml)) else TRue)
                          end
                | false =>  match (chkbol_os (getelt_at_pos  p3 ml)) with
                              | true =>  (IF (ostobol (getelt_at_pos  p1 ml)) then TRue else ((ostobol (getelt_at_pos  p3 ml))))
                              | false => (IF (ostobol (getelt_at_pos  p1 ml)) then TRue else TRue)
                            end
              end
    | false =>  match (chkbol_os (getelt_at_pos  p2 ml)) with
                  | true => match (chkbol_os (getelt_at_pos  p3 ml)) with
                              | true =>  (IF TRue then (ostobol (getelt_at_pos  p2 ml)) else ((ostobol (getelt_at_pos  p3 ml))))
                              | false => (IF TRue then (ostobol (getelt_at_pos  p2 ml)) else TRue)
                            end
                  | false =>  match (chkbol_os (getelt_at_pos  p3 ml)) with
                                | true =>  (IF TRue then TRue else ((ostobol (getelt_at_pos  p3 ml))))
                                | false => (IF TRue then TRue else TRue)
                              end
                end

  end.

(** Constructing a [pair] term from [mylist] *)

Definition pair_term_pos {n}  (m:message) (p:nat)  (ml : mylist n): message :=
  (pair m (ostomsg (getelt_at_pos  p ml))).

(** [If_then_else_M] b1 m1 ( ( m1, m2), m3) : b1 at n1, m1 at n2, m2 at n3, m3 at n4 *)

Definition ifm_nespair {m}  (p1 p2 p3 p4 :nat)(ml : mylist m) : message :=
  match (chkbol_os (getelt_at_pos  p1 ml)) with
    | true => match (chkmsg_os (getelt_at_pos  p2 ml)) with
                | true => If (ostobol (getelt_at_pos  p1 ml)) then (ostomsg (getelt_at_pos  p2 ml)) else (pair_term_pos  (pair_at_pos  p2 p3 ml) p4 ml)
                | false => (If (ostobol (getelt_at_pos  p1 ml)) then O else (pair_term_pos  (pair_term_pos  O p3 ml) p4 ml))
              end
    |false => match (chkmsg_os (getelt_at_pos  p2 ml)) with
                | true => (If TRue then (ostomsg (getelt_at_pos  p2 ml)) else (pair_term_pos  (pair_at_pos  p2 p3 ml) p4 ml))
                | false => (If TRue then O else (pair_term_pos  (pair_term_pos  O p3 ml)  p4 ml))
              end
  end.

(*Eval compute in ifm_nespair  1 3 4 5  [bol (Bvar 1) , bol (Bvar 2), msg (nonce 1), msg (nonce 2), msg (nonce 3)]. *)


(** [If_then_else_M] b1 m1 (m2, m3) : b1 at n1, m1 at n2, m2 at n3, m3 at n4 *)
Definition ifm_pair {m}  (p1 p2 p3 p4 :nat)(ml : mylist m) : message :=
  match (chkbol_os (getelt_at_pos  p1 ml)) with
    | true => match (chkmsg_os (getelt_at_pos  p2 ml)) with
                | true => (If (ostobol (getelt_at_pos  p1 ml)) then (ostomsg (getelt_at_pos  p2 ml)) else (pair_at_pos  p3 p4 ml))
                | false => (If (ostobol (getelt_at_pos  p1 ml)) then O else  (pair_at_pos  p3 p4 ml))
              end
    |false => match (chkmsg_os (getelt_at_pos  p2 ml)) with
                | true => (If TRue then (ostomsg (getelt_at_pos  p2 ml)) else (pair_at_pos  p3 p4 ml))
                | false => (If TRue then O else (pair_at_pos  p3 p4 ml))
              end
  end.

(*Eval compute in ifm_pair 1 2 3 4  [bol (Bvar 1) , bol (Bvar 2), msg (nonce 1), msg (nonce 2), msg (nonce 3)]. *)

(** Dropping the last element in [mylist] *)
Definition dropone {n:nat} (m:mylist n):(mylist (pred n)):=
  match m with
    | [] => []
    |  h: m1 => m1
  end.

(** Dropping last two elements in a [mylist] *)
Definition  droptwo {n:nat} (ml: mylist n): mylist (pred (pred n)):= (dropone (dropone ml)).

(** Apply reveal at position in [mylist] *)
(*
Definition reveal_at_pos{m} (p:nat) (ml: mylist m) : message :=
  match (chkmsg_os (getelt_at_pos  p ml)) with
    | true =>  reveal (ostomsg (getelt_at_pos p ml) )
    | false => reveal O
  end.
*)
(** Apply [to] at position in [mylist] *)
Definition to_at_pos {m} (p:nat) (ml: mylist m) : message :=
  match (chkmsg_os (getelt_at_pos  p ml)) with
    | true =>  to (ostomsg (getelt_at_pos  p ml) )
    | false => to O
  end.

(** Apply [act] at position in [mylist] *)
(*
Definition act_at_pos {m} (p:nat) (ml: mylist m) : message :=
  match (chkmsg_os (getelt_at_pos  p ml)) with
    | true =>  act (ostomsg (getelt_at_pos  p ml) )
    | false => act O
  end.

(** Apply [m] at position in [mylist] *)

Definition m_at_pos {n} (p:nat) (ml:mylist n) : message :=
  match (chkmsg_os (getelt_at_pos p ml)) with
    | true =>  m (ostomsg (getelt_at_pos p ml) )
    | false => m O
  end.
(*Eval compute in to_at_pos 4 [bol (Bvar 1) , bol (Bvar 2), msg (nonce 1), msg (nonce 2), msg (nonce 3)]. *)
*)
(** Constant function [const] *)
Definition const {X:Type}{Y:Type}(a : X) := fun _ : Y => a.
(*Eval compute in (const (nonce 0) O ). *)

(** Substitute [Bool] in [mylist] *)
Fixpoint subbol_mylist {n1:nat} (n:nat)(s:Bool)(ml: mylist n1):mylist n1 :=
  match ml with
    | [] => []
    | h:t => (subbol_os n s h) : (subbol_mylist n s t)
  end.

(** Substitute [msg] in [mylist] *)
Fixpoint submsg_mylist {n1:nat} (n:nat)(s:message)(ml: mylist n1):mylist n1 :=
  match ml with
    | [] => []
    | h:t => (submsg_os n s h) : (submsg_mylist n s t)
  end.
(*Eval compute in (subbol_mylist 1 TRue [msg O, msg (Mvar 1), bol (Bvar 1)]). *)
(*Eval compute in (submsg_os 1  ( O) (bol (Bvar 1))). *)


(** Drop last element *)
Definition drpone_last {n} (l:mylist (S n)) : mylist n :=  dropone(reverse l).

(** Project last element *)
Definition proj_one {n} (l: mylist n) : mylist 1:=
  match (reverse   l)  with
    | [] => [msg O]
    | h:t => [h]
  end.

(** Project last two *)
Definition proj_two {n} (l:mylist n) : mylist 2:=
  match (reverse l) with
    |[] => [msg O, msg O]
    | h:(t:l') => [t,h]
    | h: t => [msg O, h]
  end.

(** Drop last but one *)
Definition droplastsec {n} (l:mylist n) : mylist (pred (pred n) + pred 2) :=
  let y := (proj_two l) in
  let x := (droptwo (reverse l)) in
  let y1:= (dropone y) in
  (appMylist (reverse x) y1).

(*Eval compute in (droplastsec  [msg O, msg (Mvar 1)]). *)

(** Project last three *)
Definition proj_three {n} (l: mylist n) : mylist 3:=
  match (reverse l) with
    | [] => [msg O , msg O , msg O]
    | h : (h1 : (h2 : l1)) => [h2 , h1 , h]
    | h : (h1 : t) => [ msg O, h1 , h]
    | h : t => [msg O , msg O , h]
  end.

(** Drop last but third *)
Definition droplast3rd {n} (l:mylist n) : mylist (( pred (pred (pred n) ) ) + pred 3) :=
  let y := (proj_three l) in
  let x := (dropone (droptwo (reverse l))) in
  let y1 := (dropone y) in
  (appMylist (reverse x) y1).

(*Eval compute in (droplast3rd  [ msg (Mvar 1)]). *)

(** Construct [mylist n] where each element is [msg O] *)
Fixpoint app_n_elts (n:nat) :mylist n :=
  match n with
    | 0 => []
    | S n' => (appMylist (app_elt_front (msg O) []) (app_n_elts n'))
  end.

(*Eval compute in app_n_elts 3. *)

(** Apply [pred] on [m] for [n] times *)
Fixpoint app_pred_n (n m:nat) : nat :=
  match n with
    | 0 => m
    | S n' => (app_pred_n n' (pred m))
  end.

(** Drop [n] elements from [mylist] *)
Fixpoint drop_n_times (n :nat) {m} (l:mylist m) : mylist (app_pred_n n m) :=
  match (leb n m) with
    | true => match n with
                | 0 => l
                | S n' => let x := (dropone l) in
                          drop_n_times n' x
              end
    | false => app_n_elts (app_pred_n n  m)
  end.

(*Eval compute in drop_n_times 5 [msg O, msg O, msg O, msg O]. *)

(** First [n] elements of [mylist] **)
Definition Firstn (n:nat) {m} (l: mylist m) : mylist (app_pred_n (app_pred_n n  m) m) :=  reverse (drop_n_times (app_pred_n n m ) (reverse l)).

(** Skip or remove first [n] elements in [mylist] **)
Definition Skipn (n:nat) {m} (l: mylist m) : mylist (app_pred_n n m) :=  drop_n_times n l.

(** Swap two elements in a [mylist] *)
Definition swap_mylist (p1 p2 :nat) {m} (l:mylist m) : mylist
    (pred (app_pred_n (app_pred_n p1 m) m) +
     (1 +
      (pred
         (app_pred_n (app_pred_n (app_pred_n p1 p2) (app_pred_n p1 m))
            (app_pred_n p1 m)) +
       (1 + app_pred_n (app_pred_n p1 p2) (app_pred_n p1 m))))) :=
  let x := (Firstn p1 l) in
  let y := (Skipn p1 l) in
  let x1 := (proj_one x) in
  let x2 := reverse (dropone (reverse x)) in
  let x3 := (Firstn (app_pred_n p1 p2 ) y) in
  let x4 :=  (Skipn (app_pred_n p1 p2) y) in
  let x5 := (proj_one x3) in
  let x6 := reverse (dropone (reverse x3)) in
  x2 ++ x5 ++ x6 ++ x1 ++ x4.

(*Eval compute in swap_mylist 1 3  [ msg O, msg (Mvar 3), msg (Mvar 2), msg (Mvar 1)]. *)

(** Proj an element at a given [pos] [p] in [mylist] *)
Definition proj_at_pos (p:nat) {m} (l:mylist m) : mylist (pred (app_pred_n (app_pred_n p m) m) + app_pred_n p m) :=
  let x := (Firstn p l) in
  let y := (Skipn p l) in
  let x1 := reverse (dropone (reverse x)) in
  x1 ++ y.

(*Eval compute in proj_at_pos 3  [ msg O, msg (Mvar 3), msg (Mvar 2), msg (Mvar 1)]. *)

(** Check [equality] of two lists *)
Section def.
Variable A B :Type.
Variable  f: message -> message -> bool.
(**check if two lists equal*)
Fixpoint check_eq_listm  (l l' :Mlist)  :bool :=
  match l  with
    | nil => match l' with
               | nil => true
               | _ => false
             end
    | cons h t =>  match l' with
                     | cons h' t' => (andb (f h h') (check_eq_listm t t'))
                     | _ => false
                   end
  end.
End def.

(*

(** Check if two [Bool] terms equal *)

Fixpoint check_eq_bol (b b': Bool) : bool :=
match b with
         | Bvar n' => match b' with
                        | (Bvar n'') => if (beq_nat n' n'') then true else false
                        | _ => false
                       end
         | FAlse => match b' with
                      | FAlse => true
                      | _ => false
                    end
         | TRue => match b' with
                     | TRue => true
                     | _ => false
                    end
         | eqb b1 b2 => match b' with
                           | eqb b3 b4 => (andb (check_eq_bol b1 b3) (check_eq_bol b2 b4))
                           | _ => false
                        end
         | eqm t1 t2 => match b' with
                          | eqm t3 t4 => (andb (check_eq_msg t1 t3) (check_eq_msg t2 t4))
                          | _ => false
                         end
         | eql t1 t2 => match b' with
                          | eql t3 t4 => (andb (check_eq_msg t1 t3) (check_eq_msg t2 t4))
                          | _ => false
                        end
         | (ifb b1 b2  b3) =>  match b' with
                                            | (ifb b4 b5 b6) => (andb (check_eq_bol b1 b4) (andb (check_eq_bol b2 b5) (check_eq_bol b3 b6)))
                                            | _ => false
                                          end
         | ver t1 t2 t3 =>  match b' with
                              | ver t4 t5 t6 => (andb (check_eq_msg t1 t4) (andb (check_eq_msg t2 t5 ) (check_eq_msg t3 t6)))
                              | _ => false
                            end
         | elig b1 => match b' with
                      | elig b2 => (check_eq_msg b1 b2)
                      | _ => false
                      end
 end
with check_eq_msg ( t t' : msg ) : bool :=
   match t with
     | Mvar n =>  match t' with
                    | Mvar n' => (beq_nat n n')
                    | _  => false
                   end

    | O => match t' with
              | O => true
              | _ => false
            end
     | lnc => match t' with
                | lnc => true
                | _ => false
              end
       | lsk => match t' with
                  | lsk => true
                  | _ => false
                end
        | acc => match t' with
                   | acc => true
                   | _ => false
                 end
     | nonce n'=>  match t' with
                 | nonce n'' => if (beq_nat n' n'') then true else false
                 | _ => false
               end

     | (ifm b1 t1 t2) =>  match t' with
                                       | (ifm b2 t3 t4) => (andb (check_eq_bol b1 b2) (andb (check_eq_msg t1 t3) (check_eq_msg t2 t4)))
                                       | _ => false
                                     end
   | exp t1 t2 t3 =>  match t' with
                        | exp t4 t5 t6 => (andb (check_eq_msg t1 t4) (andb (check_eq_msg t2 t5 ) (check_eq_msg t3 t6)))
                        | _ => false
                      end

   | pair t1 t2 => match t' with
                     | pair t3 t4 => (andb (check_eq_msg t1 t3) (check_eq_msg t2 t4))
                     | _ => false
                   end

   | pi1 t1 =>  match t' with
                  | pi1 t2 =>  (check_eq_msg t1 t2)
                  | _ => false
                end

   | pi2 t1 => match t' with
                 | pi2 t2 =>  (check_eq_msg t1 t2)
                 | _ => false
              end

   | ggen t1 =>   match t' with
                    | ggen t2 =>  (check_eq_msg t1 t2)
                    | _ => false
                  end
   |rr t1 =>   match t' with
                 | rr t2 =>  (check_eq_msg t1 t2)
                 | _ => false
               end
   | new => match t' with
              | new => true
              | _ => false
            end

   | act t1 => match t' with
                 | act t2 =>  (check_eq_msg t1 t2)
                 | _ => false
               end

   | m t1 =>   match t' with
                 | m t2 =>  (check_eq_msg t1 t2)
                 | _ => false
               end
  | nc t1  =>  match t' with
                 | nc t2 =>  (check_eq_msg t1 t2)
                 | _ => false
               end
   |rs t1 =>   match t' with
                 | rs t2 =>  (check_eq_msg t1 t2)
                 | _ => false
               end

   |L t1 => match t' with
             | L t2 =>  (check_eq_msg t1 t2)
             | _ => false
            end

   | enc t1 t2 t3 =>  match t' with
                        | enc t4 t5 t6 => (andb (check_eq_msg t1 t4) (andb (check_eq_msg t2 t5 ) (check_eq_msg t3 t6)))
                        | _ => false
                      end
  |dec t1 t2 =>  match t' with
                   | dec t3 t4 => (andb (check_eq_msg t1 t3) (check_eq_msg t2 t4))
                   | _ => false
                end

   |k t1 => match t' with
              | k t2 =>  (check_eq_msg t1 t2)
              | _ => false
             end


   | to t1 => match t' with
                | to t2 =>  (check_eq_msg t1 t2)
                | _ => false
              end
   | reveal t1 =>   match t' with
                      | reveal t2 =>  (check_eq_msg t1 t2)
                      | _ => false
                    end


   | sign t1 t2 =>   match t' with
                       | sign t3 t4 => (andb (check_eq_msg t1 t3) (check_eq_msg t2 t4))
                       | _ => false
                     end

   | i n' =>  match t' with
                | i n'' => if  (beq_nat n' n'') then true else false
                | _ => false
             end

                 (** foo function symbol *)
| commit t1 t2 t3 => match t' with
                        | commit t4 t5 t6 => (andb (check_eq_msg t1 t4) (andb (check_eq_msg t2 t5 ) (check_eq_msg t3 t6)))
                        | _ => false
                      end
| open t1 t2 t3 =>  match t' with
                        | open t4 t5 t6 => (andb (check_eq_msg t1 t4) (andb (check_eq_msg t2 t5 ) (check_eq_msg t3 t6)))
                        | _ => false
                      end
| blind t1 t2 =>  match t' with
                       | blind t3 t4 => (andb (check_eq_msg t1 t3) (check_eq_msg t2 t4))
                       | _ => false
                     end
| unblind t1 t2 =>  match t' with
                       | unblind t3 t4 => (andb (check_eq_msg t1 t3) (check_eq_msg t2 t4))
                       | _ => false
                    end
| v t1 => match t' with
                | v t2 =>  (check_eq_msg t1 t2)
                | _ => false
              end
 | dcsn t1 => match t' with
                      | dcsn t2 =>  (check_eq_msg t1 t2)
                      | _ => false
                    end
|V n' =>  match t' with
                | V n'' => if  (beq_nat n' n'') then true else false
                | _ => false
             ends

| ok => match t' with
              | ok => true
              | _ => false
            end
| f l =>   match t' with
                | f l' => ( @check_eq_listm  (check_eq_msg ) l l')
                | _ => false
              end

   end.


*)

(** Check occurence of a term in a term *)
Fixpoint checkbtbol ( b':Bool) (b:Bool) : bool :=
  if (Bool_beq b' b) then true else
  match b  with
    | eqb  b1 b2 => (orb (checkbtbol b' b1) (checkbtbol b' b2))
    | eqm t1 t2 =>   (orb (checkbtmsg b' t1) (checkbtmsg b' t2))
    | ifb_then_else_ t1 t2 t3 =>  (orb (checkbtbol b' t1) (orb (checkbtbol b' t2) (checkbtbol b' t3)))
    | ver t1 t2 t3 =>   (orb (checkbtmsg b' t1)  (orb (checkbtmsg b' t2) (checkbtmsg b' t3)))
    | bver t1 t2 t3 => (orb (checkbtmsg b' t1)  (orb (checkbtmsg b' t2) (checkbtmsg b' t3)))
    | acc t1 t2 t3 t4 => (orb (orb (checkbtmsg b' t1)  (orb (checkbtmsg b' t2) (checkbtmsg b' t3))) (checkbtmsg b' t4))
    | _ => false
  end
with checkbtmsg (b :Bool) (t:message) : bool :=
       match t with
         | ifm_then_else_ b' t1 t2 => (orb (checkbtbol b b') (orb (checkbtmsg b t1) (checkbtmsg b t2)))
         | pair t1 t2 => (orb (checkbtmsg b t1) (checkbtmsg b t2))
         | pi1 t1 =>  (checkbtmsg b t1)
         | pi2 t1 =>  (checkbtmsg b t1)
         | L t1 =>   (checkbtmsg b t1)
         | to t1 =>  (checkbtmsg b t1)
         | f l => (@existsb message (checkbtmsg b) l)
         (** foo function symbol *)
         (** FOO syntax *)
         (** Vote values *)
         | V0 t1 => checkbtmsg b t1
         | V1 t1 => checkbtmsg b t1
         (** Public Key *)
         | pubkey t1 => checkbtmsg b t1
         (** Commitments *)
         | kc t1 => checkbtmsg b t1
         | comm t1 t2 => orb (checkbtmsg b t1) (checkbtmsg b t2)
         | open t1 t2 t3 => orb (orb (checkbtmsg b t1) (checkbtmsg b t2)) (checkbtmsg b t3)
         (** Shuffling *)
         | shufl t1 t2 t3 => orb (orb (checkbtmsg b t1) (checkbtmsg b t2)) (checkbtmsg b t3)
         (** Encryptions *)
         | ke t1 => checkbtmsg b t1
         | re t1 => checkbtmsg b t1
         | enc t1 t2 t3 => orb (orb (checkbtmsg b t1) (checkbtmsg b t2)) (checkbtmsg b t3)
         | dec t1 t2 =>  orb (checkbtmsg b t1) (checkbtmsg b t2)
           (** Blind Signatures *)
         | kb t1 => checkbtmsg b t1
         | rb t1 => checkbtmsg b t1
         | bsign t1 t2 t3 => orb (orb (checkbtmsg b t1) (checkbtmsg b t2)) (checkbtmsg b t3)
         | bl t1 t2 t3 => orb (orb (checkbtmsg b t1) (checkbtmsg b t2)) (checkbtmsg b t3)
         | ub t1 t2 t3 t4 => orb (orb (orb (checkbtmsg b t1) (checkbtmsg b t2)) (checkbtmsg b t3)) (checkbtmsg b t4)
         (** Signatures *)
         | ks t1 => checkbtmsg b t1
         | rs t1 => checkbtmsg b t1
         | sign t1 t2 t3 => orb (orb (checkbtmsg b t1) (checkbtmsg b t2)) (checkbtmsg b t3)
         (** zero symbol *)
         | z t1 => false
         | compl t1 => checkbtmsg b t1
         (** all other constrs *)
         | _ => true
       end.

(** Substitute term ts ([Bool]) for a term t'([Bool]) replace b' with s in b *)
Fixpoint subbol_bol'  (b' : Bool) (s: Bool) (b :Bool) : Bool :=
  if (Bool_beq b' b) then s else
    match b  with
      | eqb b1 b2 => eqb (subbol_bol' b' s b1) (subbol_bol' b' s b2)
      | eqm t1 t2 => eqm (subbol_msg' b' s t1) (subbol_msg' b' s t2)
      | ifb_then_else_ b1 b2 b3 => IF (subbol_bol' b' s b1) then (subbol_bol' b' s b2) else (subbol_bol' b' s b3)
      | ver t1 t2 t3 =>  ver (subbol_msg' b' s t1) (subbol_msg' b' s t2) (subbol_msg' b' s t3)
      | bver t1 t2 t3 => bver (subbol_msg' b' s t1) (subbol_msg' b' s t2) (subbol_msg' b' s t3)
      | acc t1 t2 t3 t4 => acc (subbol_msg' b' s t1) (subbol_msg' b' s t2) (subbol_msg' b' s t3)  (subbol_msg' b' s t4)
      | _             => b
    end
with subbol_msg' (b' : Bool )(s: Bool) (t:message) : message :=
       match t with
         | ifm_then_else_ b1 t1 t2 => (If (subbol_bol' b' s b1) then (subbol_msg' b' s t1) else (subbol_msg' b' s t2))

         | pair t1 t2 => pair (subbol_msg' b' s t1) (subbol_msg' b' s t2)
         | pi1 t1 =>  pi1 (subbol_msg' b' s t1)
         | pi2 t1 =>  pi2 (subbol_msg' b' s t1)
         | L t1 =>  L (subbol_msg' b' s t1)
         | to t1 => to  (subbol_msg' b' s t1)
         | f l =>  (f (@map message message  (subbol_msg' b' s) l))
                      (** foo function symbol *)
         (** FOO syntax *)
         (** Vote values *)
         | V0 t1 => V0 (subbol_msg' b' s t1)
         | V1 t1 => V1 (subbol_msg' b' s t1)
         (** Public Key *)
         | pubkey t1 => pubkey (subbol_msg' b' s t1)
         (** Commitments *)
         | kc t1 => kc (subbol_msg' b' s t1)
         | comm t1 t2 => comm (subbol_msg' b' s t1) (subbol_msg' b' s t2)
         | open t1 t2 t3 => open (subbol_msg' b' s t1) (subbol_msg' b' s t2) (subbol_msg' b' s t3)
         (** Shuffling *)
         | shufl t1 t2 t3 =>  shufl (subbol_msg' b' s t1) (subbol_msg' b' s t2) (subbol_msg' b' s t3)
         (** Encryptions *)
         | ke t1 => ke (subbol_msg' b' s t1)
         | re t1 => re (subbol_msg' b' s t1)
         | enc t1 t2 t3 =>  enc (subbol_msg' b' s t1) (subbol_msg' b' s t2) (subbol_msg' b' s t3)
         | dec t1 t2 =>  dec (subbol_msg' b' s t1) (subbol_msg' b' s t2)
           (** Blind Signatures *)
         | kb t1 => kb (subbol_msg' b' s t1)
         | rb t1 => rb (subbol_msg' b' s t1)
         | bsign t1 t2 t3 =>  bsign (subbol_msg' b' s t1) (subbol_msg' b' s t2) (subbol_msg' b' s t3)
         | bl t1 t2 t3 =>  bl (subbol_msg' b' s t1) (subbol_msg' b' s t2) (subbol_msg' b' s t3)
         | ub t1 t2 t3 t4 => ub (subbol_msg' b' s t1) (subbol_msg' b' s t2)  (subbol_msg' b' s t3)   (subbol_msg' b' s t4)
         (** Signatures *)
         | ks t1 => ks (subbol_msg' b' s t1)
         | rs t1 => rs (subbol_msg' b' s t1)
         | sign t1 t2 t3 => sign (subbol_msg' b' s t1) (subbol_msg' b' s t2) (subbol_msg' b' s t3)
         (** zero symbol *)
         | z t1 => z t1
         | compl t1 => compl (subbol_msg' b' s t1)
         (** all other constrs *)
         | _ => t
       end.

Fixpoint submsg_bol' (t' : message)(s:message) (b:Bool) : Bool :=
  match b with
    | eqb  b1 b2 =>  (eqb (submsg_bol' t' s b1) (submsg_bol' t' s b2))
    | eqm t1 t2 => (eqm (submsg_msg' t' s t1) (submsg_msg' t' s t2))
    | ifb_then_else_ t1 t2 t3 => (IF (submsg_bol' t' s t1) then (submsg_bol' t' s t2) else (submsg_bol' t' s t3))
    | ver t1 t2 t3 => ver  (submsg_msg' t' s t1) (submsg_msg' t' s t2) (submsg_msg' t' s t3)
    | bver t1 t2 t3 => bver (submsg_msg' t' s t1) (submsg_msg' t' s t2) (submsg_msg' t' s t3)
    | acc t1 t2 t3 t4 => acc (submsg_msg' t' s t1) (submsg_msg' t' s t2) (submsg_msg' t' s t3) (submsg_msg' t' s t4)
    | _ => b
  end
with submsg_msg' (t' : message )(s:message) (t:message) : message :=
if  (message_beq t' t)  then s else
  match t with
         | ifm_then_else_ b1 t1 t2 =>    (If (submsg_bol' t' s b1) then (submsg_msg' t' s t1) else (submsg_msg' t' s t2))
         | pair t1 t2 => pair (submsg_msg' t' s t1) (submsg_msg' t' s t2)
         | pi1 t1 =>  pi1 (submsg_msg' t' s t1)
         | pi2 t1 =>  pi2 (submsg_msg' t' s t1)
         | L t1 =>  L (submsg_msg' t' s t1)
         | to t1 => to  (submsg_msg' t' s t1)
         | f l =>  (f (@map message message  (submsg_msg' t' s) l))
         (** foo function symbol *)
         (** FOO syntax *)
         (** Vote values *)
         | V0 t1 => V0 (submsg_msg' t' s t1)
         | V1 t1 => V1 (submsg_msg' t' s t1)
         (** Public Key *)
         | pubkey t1 => pubkey (submsg_msg' t' s t1)
         (** Commitments *)
         | kc t1 => kc (submsg_msg' t' s t1)
         | comm t1 t2 => comm (submsg_msg' t' s t1) (submsg_msg' t' s t2)
         | open t1 t2 t3 => open (submsg_msg' t' s t1) (submsg_msg' t' s t2) (submsg_msg' t' s t3)
         (** Shuffling *)
         | shufl t1 t2 t3 =>  shufl (submsg_msg' t' s t1) (submsg_msg' t' s t2) (submsg_msg' t' s t3)
         (** Encryptions *)
         | ke t1 => ke (submsg_msg' t' s t1)
         | re t1 => re (submsg_msg' t' s t1)
         | enc t1 t2 t3 =>  enc (submsg_msg' t' s t1) (submsg_msg' t' s t2) (submsg_msg' t' s t3)
         | dec t1 t2 =>  dec (submsg_msg' t' s t1) (submsg_msg' t' s t2)
           (** Blind Signatures *)
         | kb t1 => kb (submsg_msg' t' s t1)
         | rb t1 => rb (submsg_msg' t' s t1)
         | bsign t1 t2 t3 =>  bsign (submsg_msg' t' s t1) (submsg_msg' t' s t2) (submsg_msg' t' s t3)
         | bl t1 t2 t3 =>  bl (submsg_msg' t' s t1) (submsg_msg' t' s t2) (submsg_msg' t' s t3)
         | ub t1 t2 t3 t4 => ub (submsg_msg' t' s t1) (submsg_msg' t' s t2)  (submsg_msg' t' s t3)   (submsg_msg' t' s t4)
         (** Signatures *)
         | ks t1 => ks (submsg_msg' t' s t1)
         | rs t1 => rs (submsg_msg' t' s t1)
         | sign t1 t2 t3 => sign (submsg_msg' t' s t1) (submsg_msg' t' s t2) (submsg_msg' t' s t3)
         | z t1 => z t1
         | compl t1 => compl (submsg_msg' t' s t1)
         (** all other constrs *)
         | _ => t
       end.

(*Eval compute in (submsg_msg' (Mvar 1) O (Mvar 2)). *)

(** Check if a term is constant *)
Definition const_bol (t:Bool) : bool :=
  match t with
    | TRue => true
    | FAlse => true
    | _ => false
  end.

Definition const_msg (t:message) : bool :=
  match t with
    | O => true
    | ONE => true
    | TWO => true
    | THREE => true
    | _ => true
  end.

(** Subterms of list of terms. *)
Section subtrm.
Variable f: message -> Mlist.
Fixpoint subtrmls (l: Mlist) : Mlist :=
  match l with
    | nil => nil
    | cons h t => (app (f h) (subtrmls t))
  end.
End subtrm.

(** list all subterms fo [msg] and [bool]. *)

Fixpoint subtrmls_bol  (t: Bool) : Mlist :=
  match t with
    | eqb  b1 b2 =>  (subtrmls_bol  b1) ++ (subtrmls_bol b2)
    | eqm t1 t2 => (app (subtrmls_msg t1) (subtrmls_msg t2) )
    | ifb_then_else_ t1 t2 t3 => (app (subtrmls_bol t1) (app (subtrmls_bol t2) (subtrmls_bol t3)))
    | ver t1 t2 t3 => (app (subtrmls_msg t1) (app (subtrmls_msg t2) (subtrmls_msg t3)))
    | bver t1 t2 t3 => (app (subtrmls_msg t1) (app (subtrmls_msg t2) (subtrmls_msg t3)))
    | acc t1 t2 t3 t4 => (app (subtrmls_msg t1) (app (subtrmls_msg t2) (subtrmls_msg t3)))
    | _ => nil
 end
with subtrmls_msg (t:message) : Mlist :=
       match t with
         | ifm_then_else_ b3 t1 t2 => (app (cons (If b3 then t1 else t2) nil)  (app (subtrmls_bol b3) (app (subtrmls_msg t1) (subtrmls_msg t2))))
         | (Mvar n') => (cons (Mvar n') nil)
         | O => (cons O nil)
         | ONE => (cons ONE nil)
         | TWO => (cons TWO nil)
         | THREE => (cons THREE nil)
         | A => (cons A nil)
         | B => (cons B nil)
         | M => (cons M nil)
         | C1 => (cons C1 nil)
         | C2 => (cons C2 nil)
         | C3 => (cons C3 nil)
         | V0 t' => (app (cons (V0 t') nil) (subtrmls_msg t'))
         | V1 t' => (app (cons (V1 t') nil) (subtrmls_msg t'))
         | pubkey t' => (app (cons (pubkey t') nil) (subtrmls_msg t'))
         | kc t' => (app (cons (kc t') nil ) (subtrmls_msg t'))
         | comm t1 t2 => (app (app (cons (comm t1 t2) nil) (subtrmls_msg t1)) (subtrmls_msg t2))
         | open t1 t2 t3 => (app (app (app (cons (open t1 t2 t3) nil) (subtrmls_msg t1)) (subtrmls_msg t2)) (subtrmls_msg t3))
         | shufl t1 t2 t3 => (app (app (app (cons (shufl t1 t2 t3) nil) (subtrmls_msg t1)) (subtrmls_msg t2)) (subtrmls_msg t3))
         | ke t' => (app (cons (ke t') nil ) (subtrmls_msg t'))
         | re t' => (app (cons (re t') nil ) (subtrmls_msg t'))
         | enc t1 t2 t3 => (app (app (app (cons (enc t1 t2 t3) nil) (subtrmls_msg t1)) (subtrmls_msg t2)) (subtrmls_msg t3))
         | dec t1 t2 => (app (app (cons (dec t1 t2) nil) (subtrmls_msg t1)) (subtrmls_msg t2))
         | bot => (cons bot nil)
         | kb t' => (app (cons (kb t') nil ) (subtrmls_msg t'))
         | rb t' => (app (cons (rb t') nil ) (subtrmls_msg t'))
         | bsign t1 t2 t3 => (app (app (app (cons (bsign t1 t2 t3) nil) (subtrmls_msg t1)) (subtrmls_msg t2)) (subtrmls_msg t3))
         | bl t1 t2 t3 => (app (app (app (cons (bl t1 t2 t3) nil) (subtrmls_msg t1)) (subtrmls_msg t2)) (subtrmls_msg t3))
         | ub t1 t2 t3 t4  =>   (app (cons ( ub t1 t2 t3 t4) nil) (app (app (subtrmls_msg t1) (app (subtrmls_msg t2) (subtrmls_msg t3))) (subtrmls_msg t4)))
         | ks t' => (app (cons (ks t') nil ) (subtrmls_msg t'))
         | rs t' => (app (cons (rs t') nil ) (subtrmls_msg t'))
         | sign t1 t2 t3 => (app (app (app (cons (sign t1 t2 t3) nil) (subtrmls_msg t1)) (subtrmls_msg t2)) (subtrmls_msg t3))
         | nonce n'=> (cons (nonce n') nil)
         | pair t1 t2 => (app (cons (pair t1 t2) nil) (app (subtrmls_msg  t1) (subtrmls_msg t2) ))
         | pi1 t1 => (app (cons (pi1 t1) nil) (subtrmls_msg t1) )
         | pi2 t1 => (app (cons (pi2 t1) nil) (subtrmls_msg t1) )
         | L t1 => (app (cons (L t1) nil)  (subtrmls_msg t1) )
         | to t1 => (app (cons (to t1) nil)  (subtrmls_msg t1) )
         | f l => ((cons (f l) (@subtrmls subtrmls_msg l)))
         | z t1 =>  (cons (z t1) nil)
         | compl t1 => (app (cons (compl t1) nil) (subtrmls_msg t1))
       end.


(** Subterms of [oursum] term. *)
Definition subtrmls_os (t:oursum) : Mlist :=
  match t with
    | msg t1 => subtrmls_msg t1
    | bol b1 =>  subtrmls_bol b1
  end.

(** Subterms of terms of type [mylist n] for some [n].*)
Fixpoint subtrmls_mylist {n} (l:mylist n) : Mlist :=
  match l with
    | [] => nil
    | h: t => (app (subtrmls_os h) (subtrmls_mylist t))
  end.

(** Check if [(nonce n)] occurs only under either [sk] or [pk] . *)
(** [msg] or [Bool]. *)
Fixpoint onlyin_pkrsk_bol (n : nat )(t:Bool) : bool :=
  match t with
    | Bvar n' => if (beq_nat n' n) then false else true
    | eqb  b1 b2 =>  (andb (onlyin_pkrsk_bol n b1)  (onlyin_pkrsk_bol n b2))
    | eqm t1 t2 => andb (onlyin_pkrsk_msg n t1) ( onlyin_pkrsk_msg n t2)
    | ifb_then_else_ t1 t2 t3 =>  (andb (onlyin_pkrsk_bol n t1) (andb (onlyin_pkrsk_bol n t2) ( onlyin_pkrsk_bol n t3)))
    | acc t1 t2 t3 t4 => (andb (andb (onlyin_pkrsk_msg n t1) (andb (onlyin_pkrsk_msg n t2) ( onlyin_pkrsk_msg n t3))) ( onlyin_pkrsk_msg n t4))
    | bver t1 t2 t3 => (andb (onlyin_pkrsk_msg n t1) (andb (onlyin_pkrsk_msg n t2) ( onlyin_pkrsk_msg n t3)))
    | ver t1 t2 t3 => (andb (onlyin_pkrsk_msg n t1) (andb (onlyin_pkrsk_msg n t2) ( onlyin_pkrsk_msg n t3)))
    | _ => true
  end
with onlyin_pkrsk_msg (n : nat )(t:message) : bool :=
       match t with
         | (Mvar n') =>  if (beq_nat n' n) then false else true
         | nonce n'=> if (beq_nat n' n) then false else true
         | ifm_then_else_ b1 t1 t2 => (andb (onlyin_pkrsk_bol n b1) (andb (onlyin_pkrsk_msg n t1) ( onlyin_pkrsk_msg n t2)))
         | pair t1 t2 =>  andb (onlyin_pkrsk_msg n t1) ( onlyin_pkrsk_msg n t2)
         | pi1 t1 => match t1 with
                       | (ks (nonce n)) => true
                       | _ => true
                     end
         | pi2 t1 => match t1 with
                       | (ks (nonce n)) => true
                       | _ => true
                     end
         | to t1 => (onlyin_pkrsk_msg n t1)
         | L t1 =>  (onlyin_pkrsk_msg n t1)
         | f l => (@forallb message (onlyin_pkrsk_msg n) l)
         | V0 t1 => (onlyin_pkrsk_msg n t1)
         | V1 t1 => (onlyin_pkrsk_msg n t1)
         | pubkey t1 => (onlyin_pkrsk_msg n t1)
         | kc t1 =>  (onlyin_pkrsk_msg n t1)
         | comm t1 t2  =>  (andb (onlyin_pkrsk_msg n t1) ( onlyin_pkrsk_msg n t2))
         | open t1 t2 t3 => (andb (onlyin_pkrsk_msg n t1) (andb (onlyin_pkrsk_msg n t2) ( onlyin_pkrsk_msg n t3)))
         | shufl t1 t2 t3 => (andb (andb (onlyin_pkrsk_msg n t1) (onlyin_pkrsk_msg n t2)) (onlyin_pkrsk_msg n t3))
         | ke t1 =>  (onlyin_pkrsk_msg n t1)
         | re t1 =>  (onlyin_pkrsk_msg n t1)
         | enc t1 t2 t3 =>  (andb (onlyin_pkrsk_msg n t1) (andb (onlyin_pkrsk_msg n t2) ( onlyin_pkrsk_msg n t3)))
         | dec t1 t2 => andb (onlyin_pkrsk_msg n t1) ( onlyin_pkrsk_msg n t2)
         | kb t1 =>  (onlyin_pkrsk_msg n t1)
         | rb t1 =>  (onlyin_pkrsk_msg n t1)
         | bsign t1 t2 t3 => (andb (andb (onlyin_pkrsk_msg n t1) ( onlyin_pkrsk_msg n t2)) (onlyin_pkrsk_msg n t3))
         | bl t1 t2 t3 => (andb (andb (onlyin_pkrsk_msg n t1) ( onlyin_pkrsk_msg n t2)) (onlyin_pkrsk_msg n t3))
         | ub t1 t2  t3 t4 => (andb (andb (andb (onlyin_pkrsk_msg n t1) ( onlyin_pkrsk_msg n t2)) (onlyin_pkrsk_msg n t3)) (onlyin_pkrsk_msg n t4))
         | ks t1 =>  (onlyin_pkrsk_msg n t1)
         | rs t1 =>  (onlyin_pkrsk_msg n t1)
         | sign t1 t2 t3 => (andb (andb (onlyin_pkrsk_msg n t1) ( onlyin_pkrsk_msg n t2)) (onlyin_pkrsk_msg n t3))
         | z t1 => true
         | compl t1 => (onlyin_pkrsk_msg n t1)
         (** Foo function protocol *)
         | _ => true
       end.

(** [oursum] *)
Definition onlyin_pkrsk_os (n : nat )(t:oursum) : bool :=
  match t with
    | msg t1 => (onlyin_pkrsk_msg n t1)
    | bol b1 => (onlyin_pkrsk_bol n b1)
  end.

(** [mylist m] for some m *)
Fixpoint onlyin_pkrsk_mylist (n : nat ){m}(t: mylist m) : bool :=
  match t with
    | []  => true
    | h: t=> (andb (onlyin_pkrsk_os n h) (onlyin_pkrsk_mylist n t))
  end.

(** insec_n returns true only if n is a subterm of in pk(n) or in sign(sk(n), ti) for some ti. Of course, n may occur as a subterm of pk(n) and sign(sk(n), t') recursively. *)
Fixpoint insec_n_bol (n : nat )(t:Bool) : bool :=
  match t with
    | eqb  b1 b2 =>  (orb (insec_n_bol n b1)  (insec_n_bol n b2))
    | eqm t1 t2 => orb (insec_n_msg n t1) ( insec_n_msg n t2)
    | ifb_then_else_ t1 t2 t3 =>  (orb (insec_n_bol n t1) (orb (insec_n_bol n t2) ( insec_n_bol n t3)))
    | acc t1 t2 t3 t4 => (orb (orb (insec_n_msg n t1) (orb (insec_n_msg n t2) ( insec_n_msg n t3))) ( insec_n_msg n t4))
    | bver t1 t2 t3 => (orb (insec_n_msg n t1) (orb (insec_n_msg n t2) ( insec_n_msg n t3)))
    | ver t1 t2 t3 => (orb (insec_n_msg n t1) (orb (insec_n_msg n t2) ( insec_n_msg n t3)))
    | _ => false
  end
with insec_n_msg (n : nat )(t:message) : bool :=
       match t with
         | (Mvar n') => false
         | nonce n'=> (beq_nat n' n)
         | ifm_then_else_ b1 t1 t2 => (orb (insec_n_bol n b1) (orb (insec_n_msg n t1) ( insec_n_msg n t2)))
         | pair t1 t2 =>  orb (insec_n_msg n t1) ( insec_n_msg n t2)
         | pi1 t1 => match t1 with
                       | (ks (nonce _)) => false
                       | _ => (insec_n_msg n t1)
                     end
         | pi2 t1 => (message_beq (ssk n) t)
         | to t1 => (insec_n_msg n t1)
         | L t1 =>  (insec_n_msg n t1)
         | f l => (@existsb message (insec_n_msg n) l)
         | V0 t1 => (insec_n_msg n t1)
         | V1 t1 => (insec_n_msg n t1)
         | pubkey t1 => (insec_n_msg n t1)
         | kc t1 =>  (insec_n_msg n t1)
         | comm t1 t2  =>  (orb (insec_n_msg n t1) ( insec_n_msg n t2))
         | open t1 t2 t3 => (orb (insec_n_msg n t1) (orb (insec_n_msg n t2) ( insec_n_msg n t3)))
         | shufl t1 t2 t3 => (orb (orb (insec_n_msg n t1) (insec_n_msg n t2)) (insec_n_msg n t3))
         | ke t1 =>  (insec_n_msg n t1)
         | re t1 =>  (insec_n_msg n t1)
         | enc t1 t2 t3 =>  (orb (insec_n_msg n t1) (orb (insec_n_msg n t2) ( insec_n_msg n t3)))
         | dec t1 t2 => orb (insec_n_msg n t1) ( insec_n_msg n t2)
         | kb t1 =>  (insec_n_msg n t1)
         | rb t1 =>  (insec_n_msg n t1)
         | bsign t1 t2 t3 => (orb (orb (insec_n_msg n t1) ( insec_n_msg n t2)) (insec_n_msg n t3))
         | bl t1 t2 t3 => (orb (orb (insec_n_msg n t1) ( insec_n_msg n t2)) (insec_n_msg n t3))
         | ub t1 t2  t3 t4 => (orb (orb (orb (insec_n_msg n t1) ( insec_n_msg n t2)) (insec_n_msg n t3)) (insec_n_msg n t4))
         | ks t1 =>  (insec_n_msg n t1)
         | rs t1 =>  (insec_n_msg n t1)
         | sign t1 t2 t3 =>  match t1 with
                           | pi2 (ks (nonce _)) =>  (orb (insec_n_msg n t2) (insec_n_msg n t3))
                           | _ => (orb (orb (insec_n_msg n t1) (insec_n_msg n t2)) (insec_n_msg n t3) )
                             end
         | z t1 => false
         | compl t1 => insec_n_msg n t1
         (** Foo function protocol *)
         | _ => false
       end.

(** [oursum]  *)
Definition  insec_n_os (n : nat )(t:oursum) : bool :=
  match t with
    | msg t1 => (insec_n_msg n t1)
    | bol b1 => (insec_n_bol n b1)
  end.

(** [mylist m] *)
Fixpoint  insec_n_mylis (n : nat ){m}(t: mylist m) : bool :=
  match t with
    | []  => false
    | h: t => (orb (insec_n_os n h)  (insec_n_mylis  n t))
  end.
(*Eval compute in (ssk 2). *)
(*Eval compute in insec_n_msg 1 (sign (ssk 2) (ssk 1) O). *)

(** remove duplicates in a list *)
  Fixpoint nodupmsg  (l : Mlist) : Mlist :=
    match l with
      | nil => nil
      | cons x xs => if checkmtlism x xs then nodupmsg xs else cons x (nodupmsg xs)
    end.

(** List of subterms of the form [sign ( sk(nonce n), t1),.....,sign ( sk(nonce n), tl)]. *)
Fixpoint list_skn_in_sign (n:nat) (l:Mlist) : Mlist :=
  match l with
    | nil => nil
    | cons h t => (app (match h with
                          | sign (pi2 (ks (nonce n'))) _ _ => if (beq_nat n' n) then (cons h nil) else nil
                          | _ => nil
                        end)
                       (list_skn_in_sign n t))
  end.

Definition distsigntrms n l := nodupmsg (list_skn_in_sign n l).

(** Definitions related to vote privacy *)
(*
Definition topsymsg_beq (t t': message ) : bool :=
   match t, t' with
     | ifm  _ _ _ , ifm _ _ _ => true
     | ifm  _ _ _ , _ => false
     | Mvar _ , Mvar _  => true
     | Mvar _ , _  => false
     | exp _ _ _ , exp _ _ _ => true
     | exp _ _ _ , _ => false
     | pair _ _, pair _ _ => true
     | pair _ _,  _ => false
     | pi1 _ , pi1 _ => true
     | pi1 _ , _ => false
     | pi2 _ , pi2 _ => true
     | pi2 _ ,  _ => false
     | trip _ _ _ , trip _ _ _ => true
     | trip _ _ _,  _ => false
     | tau1 _ , tau1 _ => true
     | tau1 _ , _ => false
     | tau2 _ , tau2 _ => true
     | tau2 _ ,  _ => false
     | tau3 _ , tau3 _ => true
     | tau3 _ ,  _ => false
     | ggen _ , ggen _ => true
     | ggen _ ,  _ =>  false
     | act _ , act _  => true
     | act _ , _  => false
     | rr _, rr _ => true
     | rr _,  _ => false
     | rs _, rs _ => true
     | rs _, _ => false
     | L _, L _ => true
     | L _, _ => false
     | m _, m _  => true
     | m _, _  => false
     | enc _ _ _, enc _ _ _ => true
     | enc _ _ _, _ => false
     | dec _ _, dec _ _ => true
     | dec _ _, _ => false
     | k _ , k _ =>  true
     | k _ , _ =>  false
     | nc _, nc _ => true
     | nc _,  _ => false
     | to _, to _ => true
     | to _, _ => false
     | reveal _, reveal _ => true
     | reveal _, _ => false
     | sign _ _ _ , sign _ _ _ =>  true
     | sign _ _ _, _ =>  false
     | f _ , f _ => true
     | f _ , _ => false
     (** foo function symbol *)
     | commit _ _ , commit _ _  => true
     | commit _ _ , _ => false
     | open _ _ , open _ _  => true
     | open _ _ , _ => false
     | blind _ _ _, blind _ _ _  =>  true
     | blind _ _ _ , _  =>  false
     | unblind _ _ _ _, unblind _ _ _ _ => true
     | unblind _ _ _ _, _  => false
     | bsign _ _ _ , bsign _ _ _ => true
     | bsign _ _ _,  _ => false
     | shuf _ _ _, shuf _ _ _ => true
     | shuf _ _ _, _ => false
     | v _ , v _=>  true
     | v _ , _ => false
     | _ , _=> msg_beq t t'
   end.

 Definition topsybol_beq (b b' : Bool) : bool :=
   match b, b' with
     | Bvar _, Bvar _ =>  true
     | eqb  _ _ , eqb _ _  =>  true
     | eqm _ _, eqm _ _ =>  true
     | ifb _ _ _, ifb _ _ _ => true
     | eql _ _ , eql _ _ => true
     | ver _ _ _, ver _ _ _ => true
     | bver _ _ _, bver _ _ _ => true
     | bacc _ _ _ _, bacc _ _ _ _  =>true
     | Bvar _,  _ =>  false
     | eqb  _ _ , _  =>  false
     | eqm _ _,   _ =>  false
     | ifb _ _ _,  _ => false
     | eql _ _ , _ => false
     | ver _ _ _,  _ => false
     | bver _ _ _, _ => false
     | bacc _ _ _ _, _  =>false
     | _ , _ => Bool_beq b b'
   end.
 Eval compute in topsymsg_beq (ifm _ _ _) O.

Definition topsyos_beq (t1 t2 : oursum): bool :=
  match t1 , t2 with
      | msg t1', msg t2' => topsymsg_beq t1' t2'
      | bol b1, bol b2 => topsybol_beq b1 b2
      | _ , _ => false
  end.

Fixpoint topsyml_beq (m:nat) (t1: message) (l:mylist m): bool :=
  match l with
    | [] => false
    | h :t => (andb (topsymsg_beq (ostomsg h) t1) (topsyml_beq _ t1 t))
  end. *)
(** * Assumptions *)
(** blinds of two indistinguishable msgs are also indistinguishable *)
(** Signatures of two indistinguishable msgs are also indistinguishable *)
Fixpoint checkostmylis (x:oursum) {n} (l:mylist n) : bool :=
  match l with
    | [] => false
    | h : t => if (oursum_beq x h) then true else (checkostmylis x t)
  end.

(** checksublis: mylist m -> mylist n -> bool *)
Fixpoint checksublis'  (l: oslist) {n} (l':mylist n) : bool :=
match (leb n n) , l with
  | true , nil => true
  | true , cons h t => if (checkostmylis h  l') then (checksublis' t l')
                     else false
  | _ , _ => false
end.

(** return the element index *)
Fixpoint eltPos  (x:oursum) {n} (l:mylist n) :nat :=
  match l with
    | [] => 0
    | h:t =>  if  (oursum_beq x h)  then 1 else S (eltPos x t)
  end.

(** sublisIndcs: mylist m -> mylist n -> list nat *)
 Fixpoint sublisIndcs' {n} (l :oslist) (l': mylist n) : list nat :=
  match  l with
    | nil => nil
    | cons h t => cons (eltPos h l')  (sublisIndcs' t l')
  end.



Section subtrm'.
Variable f: message -> oslist.
Fixpoint mapsubtrmls (l: Mlist) : oslist :=
  match l with
    | nil => nil
    | cons h t => (f h) ++ (mapsubtrmls t)
  end.
End subtrm'.

Fixpoint listmsg_os (l:Mlist): oslist:=
  match l with
    | nil => nil
    | h::t => (msg h) :: (listmsg_os t)
  end.
(** list of subtemrs of type [oursum] from [msg] and [bool] *)
Local Open Scope list_scope.
Fixpoint subtrmls'_bol (t: Bool) : oslist :=
  match t with
    | eqb b1 b2 =>  (subtrmls'_bol b1) ++ (subtrmls'_bol b2)
    | eqm t1 t2 => (app (subtrmls'_msg t1) (subtrmls'_msg t2) )
    | ifb_then_else_ t1 t2 t3 => (app (subtrmls'_bol t1) (app (subtrmls'_bol t2) (subtrmls'_bol t3)))
    | ver t1 t2 t3 => (app (subtrmls'_msg t1) (app (subtrmls'_msg t2) (subtrmls'_msg t3)))
    | bver t1 t2 t3 => (app (subtrmls'_msg t1) (app (subtrmls'_msg t2) (subtrmls'_msg t3)))
    | acc t1 t2 t3 t4 => (app (subtrmls'_msg t1) (app (subtrmls'_msg t2) (subtrmls'_msg t3)))
    | _ => nil
 end
with subtrmls'_msg (t:message) : oslist :=
       match t with
         | ifm_then_else_ b3 t1 t2 => (app (cons (msg (If b3 then t1 else t2)) nil) (app (subtrmls'_bol b3) (app (subtrmls'_msg t1) (subtrmls'_msg t2))))
         | (Mvar n') => (cons (msg (Mvar n')) nil)
         | O => (cons (msg O) nil)
         | ONE => (cons (msg ONE) nil)
         | TWO => (cons (msg TWO) nil)
         | THREE => (cons (msg THREE) nil)
         | A => (cons (msg A) nil)
         | B => (cons (msg B) nil)
         | M => (cons (msg M) nil)
         | C1 => (cons (msg C1) nil)
         | C2 => (cons (msg C2) nil)
         | C3 => (cons (msg C3) nil)
         | V0 t' => (app (cons (msg (V0 t')) nil) (subtrmls'_msg t'))
         | V1 t' => (app (cons (msg (V1 t')) nil) (subtrmls'_msg t'))
         | pubkey t' => (app (cons (msg (pubkey t')) nil) (subtrmls'_msg t'))
         | kc t' => (app (cons (msg (kc t')) nil ) (subtrmls'_msg t'))
         | comm t1 t2 => (app (app (cons (msg (comm t1 t2)) nil) (subtrmls'_msg t1)) (subtrmls'_msg t2))
         | open t1 t2 t3 => (app (app (app (cons (msg (open t1 t2 t3)) nil) (subtrmls'_msg t1)) (subtrmls'_msg t2)) (subtrmls'_msg t3))
         | shufl t1 t2 t3 => (app (app (app (cons (msg (shufl t1 t2 t3)) nil) (subtrmls'_msg t1)) (subtrmls'_msg t2)) (subtrmls'_msg t3))
         | ke t' => (app (cons (msg (ke t')) nil ) (subtrmls'_msg t'))
         | re t' => (app (cons (msg (re t')) nil ) (subtrmls'_msg t'))
         | enc t1 t2 t3 => (app (app (app (cons (msg (enc t1 t2 t3)) nil) (subtrmls'_msg t1)) (subtrmls'_msg t2)) (subtrmls'_msg t3))
         | dec t1 t2 => (app (app (cons (msg (dec t1 t2)) nil) (subtrmls'_msg t1)) (subtrmls'_msg t2))
         | bot => (cons (msg bot) nil)
         | kb t' => (app (cons (msg (kb t')) nil ) (subtrmls'_msg t'))
         | rb t' => (app (cons (msg (rb t')) nil ) (subtrmls'_msg t'))
         | bsign t1 t2 t3 => (app (app (app (cons (msg (bsign t1 t2 t3)) nil) (subtrmls'_msg t1)) (subtrmls'_msg t2)) (subtrmls'_msg t3))
         | bl t1 t2 t3 => (app (app (app (cons (msg (bl t1 t2 t3)) nil) (subtrmls'_msg t1)) (subtrmls'_msg t2)) (subtrmls'_msg t3))
         | ub t1 t2 t3 t4  =>   (app (cons (msg ( ub t1 t2 t3 t4)) nil) (app (app (subtrmls'_msg t1) (app (subtrmls'_msg t2) (subtrmls'_msg t3))) (subtrmls'_msg t4)))
         | ks t' => (app (cons (msg (ks t')) nil ) (subtrmls'_msg t'))
         | rs t' => (app (cons (msg (rs t')) nil ) (subtrmls'_msg t'))
         | sign t1 t2 t3 => (app (app (app (cons (msg (sign t1 t2 t3)) nil) (subtrmls'_msg t1)) (subtrmls'_msg t2)) (subtrmls'_msg t3))
         | nonce n'=> (cons (msg (nonce n')) nil)

         | pair t1 t2 => (app (cons (msg (pair t1 t2)) nil) (app (subtrmls'_msg  t1) (subtrmls'_msg t2) ))
         | pi1 t1 => (app (cons (msg (pi1 t1)) nil) (subtrmls'_msg t1) )
         | pi2 t1 => (app (cons (msg (pi2 t1)) nil) (subtrmls'_msg t1) )

         | L t1 => (app (cons (msg (L t1)) nil)  (subtrmls'_msg t1) )
         | to t1 => (app (cons (msg (to t1)) nil)  (subtrmls'_msg t1) )
         | f l => ((cons (msg (f l)) (@mapsubtrmls subtrmls'_msg l)))
                    (** zero symbol *)
         | z t1 => (cons (msg (z t1)) nil)
         | compl t1 => cons (msg (compl t1)) nil
       end.


(** Subterms of [oursum] term. *)
Definition subtrmls'_os (t:oursum) : oslist :=
  match t with
    | msg t1 => subtrmls'_msg t1
    | bol b1 =>  subtrmls'_bol b1
  end.

(** Subterms of terms of type [mylist n] for some [n].*)
Fixpoint subtrmls'_mylist {n} (l:mylist n) : oslist :=
  match l with
    | [] => nil
    | h: t => (app (subtrmls'_os h) (subtrmls'_mylist t))
  end.

(** Variable section *)


 (** Message Variables *)
Section mVars.
Variable f: message -> Nlist.
Fixpoint mapmVarMsg (l: Mlist) : Nlist :=
  match l with
    | nil => nil
    | h :: t => (f h) ++ (mapmVarMsg t)
  end.
End mVars.

Fixpoint mVarBol (t: Bool) : Nlist :=
  match t with
    | eqb  b1 b2 =>   (mVarBol b1)++(mVarBol b2)
    | eqm t1 t2 =>  (mVarMsg t1)++(mVarMsg t2)
    | ifb_then_else_ t1 t2 t3 =>  (mVarBol t1)++(mVarBol t2)++(mVarBol t3)
    | ver t1 t2 t3 =>  (mVarMsg t1)++(mVarMsg t2)++(mVarMsg t3)
    | bver t1 t2 t3 =>  (mVarMsg t1)++(mVarMsg t2)++(mVarMsg t3)
    | acc t1 t2 t3 t4 =>  (mVarMsg t1)++(mVarMsg t2)++(mVarMsg t3)++(mVarMsg t4)
    | _ => nil
 end
    with mVarMsg (t:message) : Nlist :=
   match t with
  | ifm_then_else_ b3 t1 t2 => (mVarBol b3) ++ (mVarMsg  t1) ++ (mVarMsg t2)
  | pair t1 t2 => (mVarMsg t1) ++ (mVarMsg t2)
  | pi1 t1 => (mVarMsg t1)
  | pi2 t1 => (mVarMsg t1)
  | to t1 => (mVarMsg t1)
  | L t1 => (mVarMsg t1)
  | f l => (@mapmVarMsg mVarMsg l)
  (** FOO syntax *)
  (** Vote values *)
  | V0 t1 => (mVarMsg t1)
  | V1 t1 => (mVarMsg t1)
  (** Public Key *)
  | pubkey t1 => (mVarMsg t1)
  (** Commitments *)
  | kc t1 => mVarMsg t1
  | comm t1 t2 =>  (mVarMsg t1) ++ (mVarMsg t2)
  | open t1 t2 t3 =>   (mVarMsg t1) ++ (mVarMsg t2) ++ (mVarMsg t3)
  (** Shuffling *)
  | shufl t1 t2 t3 =>   (mVarMsg t1) ++ (mVarMsg t2) ++ (mVarMsg t3)
  (** Encryptions *)
  | ke t1 => mVarMsg t1
  | re t1 => mVarMsg t1
  | enc t1 t2 t3 =>   (mVarMsg t1) ++ (mVarMsg t2) ++ (mVarMsg t3)
  | dec t1 t2 =>   (mVarMsg t1) ++ (mVarMsg t2)
  (** Blind Signatures *)
  | kb t1 => mVarMsg t1
  | rb t1 => mVarMsg t1
  | bsign t1 t2 t3 =>   (mVarMsg t1) ++ (mVarMsg t2) ++ (mVarMsg t3)
  | bl t1 t2 t3 =>   (mVarMsg t1) ++ (mVarMsg t2) ++ (mVarMsg t3)
  | ub t1 t2 t3 t4 =>    (mVarMsg t1) ++ (mVarMsg t2) ++ (mVarMsg t3) ++ (mVarMsg t4)
  (** Signatures *)
  | ks t1 => mVarMsg t1
  | rs t1 => mVarMsg t1
  | sign t1 t2 t3 =>  (mVarMsg t1) ++ (mVarMsg t2) ++ (mVarMsg t3)
  (* zero symbol*)
  | z t1 =>  mVarMsg t1
  | compl t1 => mVarMsg t1
  (** all other constrs *)
  | Mvar n' => cons n' nil
  | _ => nil
   end.

(** list free variables in a term of type [oursum] *)
Definition mVarOs (t:oursum) :Nlist :=
  match t with
    | msg t1 => mVarMsg t1
    | bol b1 => mVarBol b1
  end.

(** list free variables in a term of type [mylist] *)
Fixpoint mVarMylist {n} (l:mylist n) : Nlist :=
  match l with
    | [] => nil
    | h : t => (mVarOs h)++(mVarMylist t)
  end.

(** Bvars ****)
Section bMars.
Variable f: message -> Nlist.

Fixpoint mapbVarMsg (l: Mlist) : Nlist :=
  match l with
    | nil => nil
    | h :: t => (f h) ++ (mapbVarMsg t)
  end.
End bMars.

Fixpoint bVarBol (t: Bool) : Nlist :=
  match t with
    | eqb  b1 b2 =>   (bVarBol b1)++(bVarBol b2)
    | eqm t1 t2 =>  (bVarMsg t1)++(bVarMsg t2)
    | ifb_then_else_ t1 t2 t3 =>  (bVarBol t1)++(bVarBol t2)++(bVarBol t3)
    | ver t1 t2 t3 =>  (bVarMsg t1)++(bVarMsg t2)++(bVarMsg t3)
    | bver t1 t2 t3 =>  (bVarMsg t1)++(bVarMsg t2)++(bVarMsg t3)
    | acc t1 t2 t3 t4 =>  (bVarMsg t1)++(bVarMsg t2)++(bVarMsg t3)++(bVarMsg t4)
    | Bvar n' => cons n' nil
    | _ => nil
 end
 with bVarMsg (t:message) : Nlist :=
   match t with
  | ifm_then_else_ b3 t1 t2 => (bVarBol b3) ++ (bVarMsg  t1) ++ (bVarMsg t2)
  | pair t1 t2 => (bVarMsg t1) ++ (bVarMsg t2)
  | pi1 t1 => (bVarMsg t1)
  | pi2 t1 => (bVarMsg t1)
  | L t1 => (bVarMsg t1)
  | f l => (@mapbVarMsg bVarMsg l)
  (** FOO syntax *)
  (** Vote values *)
  | V0 t1 => (bVarMsg t1)
  | V1 t1 => (bVarMsg t1)
  (** Public Key *)
  | pubkey t1 => (bVarMsg t1)
  (** Commitments *)
  | kc t1 => bVarMsg t1
  | comm t1 t2 =>  (bVarMsg t1) ++ (bVarMsg t2)
  | open t1 t2 t3 =>   (bVarMsg t1) ++ (bVarMsg t2) ++ (bVarMsg t3)
  (** Shuffling *)
  | shufl t1 t2 t3 =>   (bVarMsg t1) ++ (bVarMsg t2) ++ (bVarMsg t3)
  (** Encryptions *)
  | ke t1 => bVarMsg t1
  | re t1 => bVarMsg t1
  | enc t1 t2 t3 =>   (bVarMsg t1) ++ (bVarMsg t2) ++ (bVarMsg t3)
  | dec t1 t2 =>   (bVarMsg t1) ++ (bVarMsg t2)
  (** Blind Signatures *)
  | kb t1 => bVarMsg t1
  | rb t1 => bVarMsg t1
  | bsign t1 t2 t3 =>   (bVarMsg t1) ++ (bVarMsg t2) ++ (bVarMsg t3)
  | bl t1 t2 t3 =>   (bVarMsg t1) ++ (bVarMsg t2) ++ (bVarMsg t3)
  | ub t1 t2 t3 t4 =>    (bVarMsg t1) ++ (bVarMsg t2) ++ (bVarMsg t3) ++ (bVarMsg t4)
  (** Signatures *)
  | ks t1 => bVarMsg t1
  | rs t1 => bVarMsg t1
  | sign t1 t2 t3 =>  (bVarMsg t1) ++ (bVarMsg t2) ++ (bVarMsg t3)
  (** zeo symbol *)
  | z t1 => nil
  | compl t1 => bVarMsg t1
  (** all other constrs *)
  | _ => nil
   end.

(** list free variables in a term of type [oursum] *)
Definition bVarOs (t:oursum) :Nlist :=
  match t with
    | msg t1 => bVarMsg t1
    | bol b1 => bVarBol b1
  end.

(** list free variables in a term of type [mylist] *)
Fixpoint bVarMylist {n} (l:mylist n) : Nlist :=
  match l with
    | [] => nil
    | h : t => (bVarOs h) ++ (bVarMylist t)
  end.

(** Computation of a list without duplication *)
Fixpoint nodup (l:Nlist) : Nlist :=
  match l with
    | nil => nil
    | h :: t => if (leb 1 (@count_occ nat eq_nat_dec t h) ) then (nodup t) else (cons h (nodup t))
  end.

Definition distMvars {n} (l :mylist n) := nodup (mVarMylist l).

(*Eval compute in (If TRue then O else O). *)

(** replace name n with n' in Bools and messages *)



(** Substitution: (nonce n) <- (nonce n') in t *)
Reserved Notation "'(' n '<-' s ')' t" (at level 0).
Reserved Notation "'[' n '<-' s ']' t" (at level 0).

Fixpoint subname_bol (n : nat )(s:nat) (b:Bool) : Bool :=
  match b with
    | eqb  b1 b2 =>  eqb  ([n<- s]b1) ([n<- s]b2)
    | eqm t1 t2 => eqm ( (n<- s ) t1) (( n<-s ) t2)
    | ifb_then_else_ t1 t2 t3 => ifb_then_else_  ([n<-s]t1) ([n<-s] t2) ([n<-s]t3)
    | ver t1 t2 t3 => ver ((n<-s)t1) ((n<-s)t2) ((n<-s)t3)
    | bver t1 t2 t3 => bver ((n<-s)t1) ((n<-s)t2) ((n<-s)t3)
    | acc t1 t2 t3 t4 =>  acc ((n<-s)t1) ((n<-s)t2) ((n<-s)t3) ((n<-s)t4)
    | _ => b
  end
    where "'[' x '<-' s ']' t" := (subname_bol x s t)
with subname_msg (n : nat )(s:nat) (t:message) : message :=
  match t with
       (** Core syntax *)
  | nonce n' => if (beq_nat n' n) then (nonce s) else t
  | ifm_then_else_ b1 t1 t2 =>  ifm_then_else_ ([n<-s] b1) ((n<- s ) t1) (( n<-s ) t2)
  | pair t1 t2  => pair ((n<- s ) t1) ( ( n<-s ) t2)
  | pi1 t1 => pi1 ((n<- s ) t1)
  | pi2 t2 => pi2 (( n<-s ) t2)
  | to t2 => to (( n<-s ) t2)
  | L t1 => L ((n<- s ) t1)
  | f l => (f (@map message message  (subname_msg n s) l))
  (** FOO syntax *)
  (** Vote values *)
  | V0 t1 => V0 ((n<- s ) t1)
  | V1 t1 => V1 (( n<-s ) t1)
  (** Public Key *)
  | pubkey t1 => pubkey ((n<- s ) t1)
  (** Commitments *)
  | kc t1 => kc ((n<- s ) t1)
  | comm t1 t2 => comm ((n<- s ) t1) (( n<-s ) t2)
  | open t1 t2 t3 => open ((n<- s ) t1) (( n<-s ) t2) (( n<-s ) t3)
  (** Shuffling *)
  | shufl t1 t2 t3 => shufl ((n<- s ) t1) (( n<-s ) t2) (( n<-s ) t3)
  (** Encryptions *)
  | ke t1 => ke ((n<- s ) t1)
  | re t1 => re ((n<- s ) t1)
  | enc t1 t2 t3 => enc ((n<- s) t1) (( n<-s ) t2) (( n<-s ) t3)
  | dec t1 t2 => dec ((n<- s ) t1) (( n<-s ) t2)
  (** Blind Signatures *)
  | kb t1 => kb ((n<- s ) t1)
  | rb t1 => rb ((n<- s ) t1)
  | bsign t1 t2 t3 => bsign ((n<- s) t1) (( n<-s) t2) ((n<-s) t3)
  | bl t1 t2 t3 => bl ((n<- s) t1) (( n<-s) t2) ((n<-s) t3)
  | ub t1 t2 t3 t4 => ub ((n<- s) t1) (( n<-s) t2) ((n<-s) t3) ((n<-s) t4)
  (** Signatures *)
  | ks t1 => ks ((n<- s ) t1)
  | rs t1 => rs ((n<- s ) t1)
  | sign t1 t2 t3 => sign ((n<- s) t1) (( n<-s) t2) ((n<-s) t3)
  | compl t1 => compl ((n<- s ) t1)
  (** zero symbol *)
  | z t1 => z t1
  (** all other constrs *)
  | _ => t
  end
  where "'(' x '<-' s ')' t" := (subname_msg x s t).

(** Substitution: x <- s in t, x is a name, t is of [oursum] *)
Definition subname_os (n:nat)(s:nat) (t:oursum):oursum :=
match t with
| msg t1 => msg ((n <- s) t1)
| bol b1 => bol ([n <- s] b1)
end.

(** Substitution in [ilist message n'] *)
Fixpoint subname_mylist {n':nat} (n:nat)(s:nat)(l: mylist n') : mylist n' :=
match l with
| [] => []
| h:t => (match h with
           | msg t' => msg ((n <- s)t')
           | bol b  => bol ([n<- s]b)
           end):(subname_mylist n s t)
end.
(*Eval compute in (subname_msg 1 O  (f [ (Mvar 1) ; (nonce 2) ; (nonce 1)])). *)
(*Eval compute in  ( ( 1 <- 2 ) (nonce 1) ). *)
(*Eval compute in (O, O, O). *)
(*Eval compute in { O }_2^^3. *)

