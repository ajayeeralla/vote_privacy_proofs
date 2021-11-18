Require Export prop_19.
Require Import List.
Import ListNotations.
Require Import Coq.Init.Datatypes.

Declare Scope destruct_scope.
Delimit Scope destruct_sope with destr.

Inductive prodOsl: Type :=
| mypair (l1 l2: oslist).

Definition pi1ProdOsl (p: prodOsl): oslist :=
  match p with
  | mypair l1 l2 => l1
  end.

Notation "'fst' p" := (pi1ProdOsl p) (at level 0): destruct_scope.

Definition pi2ProdOsl (p: prodOsl): oslist :=
  match p with
  | mypair l1 l2 => l2
  end.

Notation "'snd' p" := (pi2ProdOsl p) (at level 0): destruct_scope.

Inductive prodMylist: Type :=
| pairMylist (n: nat) (l1 l2: mylist n).

Definition mylength (p: option (prodMylist)) : nat :=
  match p with
  | Some (pairMylist m _ _) => m
  | None => 0
  end.

Definition pi1ProdMylist (p: option (prodMylist)): mylist (mylength p) :=
  match p with
  | Some (pairMylist _ l1 _) => l1
  | _ => []
  end.

Definition pi2ProdMylist (p: option (prodMylist)): mylist (mylength p) :=
  match p with
  | Some (pairMylist _ _ l2) => l2
  | _ => []
  end.

Fixpoint oslToMylist (l1 l2: oslist): option (prodMylist) :=
  match l1, l2 with
  | nil, nil => Some (pairMylist 0 [] [])
  | h1::t1, h2::t2 => match oslToMylist t1 t2 with
                      | Some (pairMylist m t3 t4) => Some (pairMylist (S m) (h1:t3) (h2:t4))
                      | None => None
                      end
  | _, _ => None
  end.

Open Scope destruct_scope.
 Fixpoint remove (t1 t2: oursum) (l1 l2: oslist): prodOsl :=
  match l1, l2 with
  | h1::tl1, h2::tl2 => if ((h1 =?= t1) && (h2 =?=t2))%bool
                          then (mypair tl1 tl2)
                          else let g:= remove t1 t2 tl1 tl2 in
                               (mypair (h1::fst g) (h2::snd g))
  | _, _ => mypair l1 l2
  end.

Definition remThenApp (t1 t2: oursum) (l1 l2: oslist): prodOsl :=
  let g := remove t1 t2 l1 l2 in
  mypair (t1::fst g) (t2::snd g).

Fixpoint remThenAppList (l1 l2 l1' l2': oslist): prodOsl :=
  match l1, l2 with
  | h1::t1, h2::t2 => let p := remThenApp h1 h2 l1' l2' in
                      remThenAppList t1 t2 (fst p) (snd p)
  | _, _ => mypair l1' l2'
  end.
(* Remove duplicates in my way *)
Fixpoint checkBtMlist (b: Bool) (l: Blist): bool :=
  match l with
  | nil => false
  | h::t => (checkbtbol b h) || (checkBtMlist b t)
  end.

Fixpoint nodupBol (l: Blist): Blist :=
  match l with
  | nil => nil
  | h::t => if checkBtMlist h t then nodupBol t else h:: (nodupBol t)
  end.
Fixpoint checkMtOsl (t: message) (l: oslist): bool :=
  match l with
  | nil => false
  | h::tl => match h with
             | msg t' => (checkmtmsg t t') || checkMtOsl t tl
             | bol b => (checkmtbol t b) || checkMtOsl t tl
             end
  end.
Fixpoint checkBtOsl (b: Bool) (l: oslist): bool :=
  match l with
  | nil => false
  | h::tl => match h with
             | bol b' => checkbtbol b b' || checkBtOsl b tl
             | msg t => checkbtmsg b t || checkBtOsl b tl
             end
  end.

Fixpoint checkOsList (os: oursum) (l: oslist): bool :=
  match l with
  | nil => false
  | h::t => match h with
            | msg t => checkMtOsl t l
            | bol b => checkBtOsl b l
            end
  end.

Fixpoint nodupOsl l : oslist :=
  match l with
  | nil => nil
  | h::t => if checkOsList h t then nodupOsl t else h::(nodupOsl t)
  end.

(* This works great  *)
Fixpoint In (a: oursum) (l: oslist): bool :=
  match l with
  | [ ]%list => false
  | h::t => oursum_beq h a || In a t
  end.
Fixpoint noDup (l: oslist): oslist :=
  match l with
  | [ ] => [ ]
  | h::t => if In h t then noDup t else h::(noDup t)
  end.
(* Check map. *)

Section destrComm.
Variable f: message -> message -> prodOsl.
Fixpoint destrComm_f_all (l1 l2: list message): prodOsl :=
  match l1, l2 with
  | h1::t1, h2::t2 => let p:= f h1 h2 in
                      let rec:= destrComm_f_all t1 t2 in
                      mypair ((fst p)++(fst rec)) ((snd p)++(snd rec))
  | _, _ => mypair nil nil
  end.
End destrComm.

(* Compute height of the Abstract Syntax Tree (AST) *)
(* if h (t) = 0 if t is a ground constructor of arity 0, z(w) for any term w, Mvar, Bvar, or nonce constructor *)
(*          = max{h(t1), and so on, h(tn)} + 1 if t = f(t1, and so on tn) *)
(* Import ListNotations. *)

Fixpoint maxList (l: Nlist) : nat :=
  match l with
  | [ ] => 0
  | h::t => let g := maxList t in
              (max h g)
  end.
Open Scope msg_scope.
Fixpoint heightMsg (t: message) : nat :=
  match t with
  | Mvar _ => 0
  | nonce _ => 0
  | ifm_then_else_ b t1 t2 => let h w := heightMsg w in
                         maxList[ (heightBol b); (h t1); (h t2)] + 1
  | (t1, t2) => (max (heightMsg t1) (heightMsg t2)) + 1
  | pi1 t1 => (heightMsg t1) + 1
  | pi2 t1 => (heightMsg t1) + 1
  | to t1 => (heightMsg t1) + 1
  | L t1 => (heightMsg t1) + 1
  | f l => maxList (map heightMsg l) + 1
  | ONE => 0
  | TWO => 0
  | THREE => 0
  | A => 0
  | B => 0
  | M => 0
  | C1 => 0
  | C2 => 0
  | C3 => 0
  | V0 _ => 0
  | V1 _ => 0
  | pubkey _ => 0
  | kc t1 => (heightMsg t1) + 1
  | comm t1 t2 => (max (heightMsg t1) (heightMsg t2)) + 1
  | open t1 t2 t3 => let h w := heightMsg w in
                     maxList[ (h t1); (h t2); (h t3)] + 1
  | shufl t1 t2 t3 => let h w := heightMsg w in
                     maxList[ (h t1); (h t2); (h t3)] + 1

  | ke t1 => (heightMsg t1) + 1
  | re t1 => (heightMsg t1) + 1
  | enc t1 t2 t3 => let h w := heightMsg w in
                     maxList[ (h t1); (h t2); (h t3)] + 1
  | dec t1 t2 => (max (heightMsg t1) (heightMsg t2)) + 1
  | bot => 0
  | kb t1 => (heightMsg t1) + 1
  | rb t1 => (heightMsg t1) + 1
  | bsign t1 t2 t3 => let h w := heightMsg w in
                      maxList[ (h t1); (h t2); (h t3)] + 1
  | bl t1 t2 t3 => let h w := heightMsg w in
                   maxList[ (h t1); (h t2); (h t3)] + 1
  | ub t1 t2 t3 t4 => let h w := heightMsg w in
                   maxList[ (h t1); (h t2); (h t3); (h t4)] + 1
  | ks t1 => (heightMsg t1) + 1
  | rs t1 => (heightMsg t1) + 1
  | sign t1 t2 t3 => let h w := heightMsg w in
                      maxList[ (h t1); (h t2); (h t3)] + 1
  | z _ => 0
  | compl t1 => (heightMsg t1) + 1
  | _ => 0
  end
with heightBol (b: Bool) : nat :=
       match b with
       | Bvar _ => 0
       | TRue => 0
       | FAlse => 0
       | eqb b1 b2 => (max (heightBol b1) (heightBol b2)) + 1
       | eqm t1 t2 => (max (heightMsg t1) (heightMsg t2)) + 1
       | ifb_then_else_ b1 b2 b3 => let h w := heightBol w in
                                    maxList[ (h b1); (h b2); (h b3)] + 1
       | acc t1 t2 t3 t4 => let h w := heightMsg w in
                           maxList[ (h t1); (h t2); (h t3); (h t4)] + 1
       | bver t1 t2 t3 => let h w := heightMsg w in
                          maxList[ (h t1); (h t2); (h t3)] + 1
       | ver t1 t2 t3 => let h w := heightMsg w in
                         maxList[ (h t1); (h t2); (h t3)] + 1
       end.

(* Compute heightMsg (f [O; comm (nonce 0) O]). *)

Definition heightOs (os: oursum) : nat :=
  match os with
  | msg t => heightMsg t
  | bol b => heightBol b
  end.

Fixpoint maxHeightMylist {m} (l: mylist m) : nat :=
                              match l with
                               | [] => 0
                               | h:t => let h' := maxHeightMylist t in
                                        max (heightOs h) h'
                              end.


(** Destruct n level down **)
Fixpoint bfsDestrCommBol (n: nat) (b1 b2: Bool): prodOsl :=
  if Bool_beq b1 b2 then mypair [ ] [ ]
  else if (n =? 0)%nat then mypair (cons (bol b1) nil) (cons (bol b2) nil)
       else
         match b1, b2 with
         | ifb_then_else_ b01 b02 b03, ifb_then_else_ b11 b12 b13 => let posl1 := bfsDestrCommBol (pred n) b01 b11 in
                                                                     let posl2 := bfsDestrCommBol (pred n)  b02 b12 in
                                                                     let posl3 := bfsDestrCommBol (pred n) b03 b13 in
                                                                     mypair ((fst posl1)++(fst posl2)++(fst posl3)) ((snd posl1)++(snd posl2)++(snd posl3))
         | eqb b01 b02, eqb b11 b12 => let posl1 := bfsDestrCommBol (pred n) b01 b11 in
                                       let posl2 := bfsDestrCommBol (pred n) b02 b12 in
                                       mypair ((fst posl1)++(fst posl2)) ((snd posl1)++(snd posl2))
         | eqm t01 t02, eqm t11 t12 =>  let posl1 := bfsDestrCommMsg (pred n) t01 t11 in
                                        let posl2 := bfsDestrCommMsg (pred n) t02 t12 in
                                        mypair ((fst posl1)++(fst posl2)) ((snd posl1)++(snd posl2))
         | ver t01 t02 t03, ver t11 t12 t13 => let posl1 := bfsDestrCommMsg (pred n) t01 t11 in
                                               let posl2 := bfsDestrCommMsg (pred n) t02 t12 in
                                               let posl3 := bfsDestrCommMsg (pred n) t03 t13 in
                                               mypair ((fst posl1)++(fst posl2)++(fst posl3)) ((snd posl1)++(snd posl2)++(snd posl3))
         | bver t01 t02 t03, bver t11 t12 t13 => let posl1 := bfsDestrCommMsg (pred n) t01 t11 in
                                                 let posl2 := bfsDestrCommMsg (pred n) t02 t12 in
                                                 let posl3 := bfsDestrCommMsg (pred n) t03 t13 in
                                                 mypair ((fst posl1)++(fst posl2)++(fst posl3)) ((snd posl1)++(snd posl2)++(snd posl3))
         | acc t01 t02 t03 t04, acc t11 t12 t13 t14 => let posl1 := bfsDestrCommMsg (pred n) t01 t11 in
                                                       (* let posl2 := bfsDestrCommMsg (pred n) t02 t12 in *)
                                                       (* let posl3 := bfsDestrCommMsg (pred n) t03 t13 in *)
                                                       let posl4 := bfsDestrCommMsg (pred n) t04 t14 in
                                                       (* mypair ((fst posl1)++(fst posl2)++(fst posl3)++(fst posl4)) ((snd posl1)++(snd posl2)++(snd posl3)++(snd posl4)) *)
                                                              mypair ((fst posl1)++(fst posl4)) ((snd posl1)++(snd posl4))
         | _, _ => mypair (cons (bol b1) nil) (cons (bol b2) nil)
         end
with bfsDestrCommMsg (n: nat) (t1 t2: message): prodOsl :=
       let res:= mypair (cons (msg t1) nil) (cons (msg t2) nil) in
       if message_beq t1 t2 then mypair [ ] [ ]
       else if (n =? 0)%nat then res
            else
              match t1, t2 with
              | open t01 t02 t03, open t11 t12 t13 => let posl1 := bfsDestrCommMsg (pred n) t01 t11 in
                                                      let posl2 := bfsDestrCommMsg (pred n) t02 t12 in
                                                      let posl3 := bfsDestrCommMsg (pred n) t03 t13 in
                                                      mypair ((fst posl1)++(fst posl2)++(fst posl3)) ((snd posl1)++(snd posl2)++(snd posl3))
              | shufl t01 t02 t03, shufl t11 t12 t13 => let posl1 := bfsDestrCommMsg (pred n) t01 t11 in
                                                        let posl2 := bfsDestrCommMsg (pred n) t02 t12 in
                                                        let posl3 := bfsDestrCommMsg (pred n) t03 t13 in
                                                        mypair ((fst posl1)++(fst posl2)++(fst posl3)) ((snd posl1)++(snd posl2)++(snd posl3))
              | enc t01 t02 t03, enc t11 t12 t13 => let posl1 := bfsDestrCommMsg (pred n) t01 t11 in
                                               (* let posl2 := bfsDestrCommMsg (pred n) t02 t12 in *)
                                               (* let posl3 := bfsDestrCommMsg (pred n) t03 t13 in *)
                                                    (* mypair ((fst posl1)++(fst posl2)++(fst posl3)) ((snd posl1)++(snd posl2)++(snd posl3)) *)
                                                           mypair (fst posl1) (snd posl1)
              | dec t01 t02, dec t11 t12 =>  let posl1 := bfsDestrCommMsg (pred n) t01 t11 in
                                             (* let posl2 := bfsDestrCommMsg (pred n) t02 t12 in *)
                                             mypair (fst posl1) (snd posl1)
              | bsign t01 t02 t03, bsign t11 t12 t13 => let posl1 := bfsDestrCommMsg (pred n) t01 t11 in
                                                        let posl2 := bfsDestrCommMsg (pred n) t02 t12 in
                                                        let posl3 := bfsDestrCommMsg (pred n) t03 t13 in
                                                        mypair ((fst posl1)++(fst posl2)++(fst posl3)) ((snd posl1)++(snd posl2)++(snd posl3))
              | bl t01 t02 t03, bl t11 t12 t13 => let posl1 := bfsDestrCommMsg (pred n) t01 t11 in
                                                  (* let posl2 := bfsDestrCommMsg (pred n) t02 t12 in *)
                                                  (* let posl3 := bfsDestrCommMsg (pred n) t03 t13 in *)
              (* mypair ((fst posl1)++(fst posl2)++(fst posl3)) ((snd posl1)++(snd posl2)++(snd posl3)) *)
                                                  mypair (fst posl1) (snd posl1)

              | sign t01 t02 t03, sign t11 t12 t13 => let posl1 := bfsDestrCommMsg (pred n) t01 t11 in
                                                      let posl2 := bfsDestrCommMsg (pred n) t02 t12 in
                                                      let posl3 := bfsDestrCommMsg (pred n) t03 t13 in
                                                      mypair ((fst posl1)++(fst posl2)++(fst posl3)) ((snd posl1)++(snd posl2)++(snd posl3))
              | ub t01 t02 t03 t04, ub t11 t12 t13 t14 => let posl1 := bfsDestrCommMsg (pred n) t01 t11 in
                                                          (* let posl2 := bfsDestrCommMsg (pred n) t02 t12 in *)
                                                          (* let posl3 := bfsDestrCommMsg (pred n) t03 t13 in *)
                                                          let posl4 := bfsDestrCommMsg (pred n) t04 t14 in
                                                          mypair ((fst posl1)++(fst posl4)) ((snd posl1)++(snd posl4))
              | ifm_then_else_ b00 t01 t02, ifm_then_else_ b10 t11 t12 => let posl1 := bfsDestrCommBol (pred n) b00 b10 in
                                                                          let posl2 := bfsDestrCommMsg (pred n) t01 t11 in
                                                                          let posl3 := bfsDestrCommMsg (pred n) t02 t12 in
                                                                          mypair ((fst posl1)++(fst posl2)++(fst posl3)) ((snd posl1)++(snd posl2)++(snd posl3))
              | (t01, t02), (t11, t12) => let posl1 := bfsDestrCommMsg (pred n) t01 t11 in
                                          let posl2 := bfsDestrCommMsg (pred n) t02 t12 in
                                          mypair ((fst posl1)++(fst posl2)) ((snd posl1)++(snd posl2))
              | pi1 t01, pi1 t11 => let posl1 := bfsDestrCommMsg (pred n) t01 t11 in
                                    mypair (fst posl1) (snd posl1)
              | pi2 t01, pi2 t11 => let posl1 := bfsDestrCommMsg (pred n) t01 t11 in
                                    mypair (fst posl1) (snd posl1)
              | (f l1), (f l2) => let res1 := (@destrComm_f_all (bfsDestrCommMsg (pred n)) l1 l2) in
                                  let left := fst res1 in
                                  let right := snd res1 in
                                  mypair left right
              | comm t01 t02, comm t11 t12 => let res1 := mypair (cons (msg t01) nil) (cons (msg t11) nil) in
                                              if message_beq t02 t12 then
                                                match t01, t11 with
                                                | V0 t001, V1 t111 => if message_beq t001 t111 then mypair [ ] [ ] else res1
                                                | V1 t001, V0 t111 => if message_beq t001 t111 then mypair [ ] [ ] else res1
                                                | _, _ => res
                                                end
                                              else res
              | _, _ => res
              end.

Definition bfsdestrCommOs (n: nat) (os1 os2: oursum): prodOsl :=
  if oursum_beq os1 os2 then (mypair [ ] [ ]) else
  match os1, os2 with
  | msg t00, msg t10 => bfsDestrCommMsg n t00 t10
  | bol b00, bol b10 => bfsDestrCommBol n b00 b10
  | _, _ => mypair [ ] [ ]
  end.

Fixpoint bfsdestrCommOsl (n: nat) (l1 l2: oslist): prodOsl :=
  match l1, l2 with
  | h1::t1, h2::t2 => let rec:= bfsdestrCommOsl n t1 t2 in
                      let curr:= bfsdestrCommOs n h1 h2 in
                      let l00:= fst curr in
                      let l01:= fst rec in
                      let l10:= snd curr in
                      let l11:= snd rec in
                      (* let left:= noDup (l00 ++ l01) in
                      let right:= noDup (l10 ++ l11) in
                      mypair left right *)
                      (* remThenAppList l00 l10 l01 l11 *)
                      mypair ((fst curr)++(fst rec)) ((snd curr)++(snd rec))
  | _, _ => mypair [ ] [ ]
  end.

Axiom funcAppbfsDestrComm: forall n {m} (l1 l2: mylist m), let l1' := conv_mylist_listos l1 in
                                                         let l2' := conv_mylist_listos l2 in
                                                         let x := bfsdestrCommOsl n l1' l2' in
                                                         let y := oslToMylist (pi1ProdOsl x) (pi2ProdOsl x) in
                                                         ((mylength y) =? 0 = false)%nat -> (pi1ProdMylist y) ~ (pi2ProdMylist y) -> l1 ~ l2.

Ltac aplyBfsDestrComm levelDown :=
  match goal with
  |[|- ?X ~ ?Y] => apply funcAppbfsDestrComm with (n:= levelDown) (l1:= X) (l2:=Y); simpl; try auto
  end.


(* Destruct terms for applying CCA1 and CCA2 of encryptions *)

Section destrEnc.
Variable f: nat -> nat -> message -> message -> prodOsl.
Fixpoint destrEnc_f_all (a r: nat) (l1 l2: list message): prodOsl :=
  match l1, l2 with
  | h1::t1, h2::t2 => let p:= f a r h1 h2 in
                      let rec:= destrEnc_f_all a r t1 t2 in
                      mypair ((fst p)++(fst rec)) ((snd p)++(snd rec))
  | _, _ => mypair nil nil
  end.
End destrEnc.
Open Scope msg_scope.
(* a is used to represent the agent name and r is used to randomize encryption *)
Fixpoint destrEncBol (a r: nat) (b1 b2: Bool): prodOsl:=
  if Bool_beq b1 b2 then mypair [ ] [ ] else
  match b1, b2 with
  | IF b01 then b02 else b03, IF b11 then b12 else b13 => let posl1 := destrEncBol a r b01 b11 in
                                                          let posl2 := destrEncBol a r b02 b12 in
                                                          let posl3 := destrEncBol a r b03 b13 in
                                                          mypair ((fst posl1)++(fst posl2)++(fst posl3)) ((snd posl1)++(snd posl2)++(snd posl3))
  | eqb b01 b02, eqb b11 b12 => let posl1 := destrEncBol a r b01 b11 in
                                let posl2 := destrEncBol a r b02 b12 in
                                mypair ((fst posl1)++(fst posl2)) ((snd posl1)++(snd posl2))
  | eqm t01 t02, eqm t11 t12 =>  let posl1 := destrEncMsg a r t01 t11 in
                                 let posl2 := destrEncMsg a r t02 t12 in
                                 mypair ((fst posl1)++(fst posl2)) ((snd posl1)++(snd posl2))
  | ver t01 t02 t03, ver t11 t12 t13 => let posl1 := destrEncMsg a r t01 t11 in
                                        let posl2 := destrEncMsg a r t02 t12 in
                                        let posl3 := destrEncMsg a r t03 t13 in
                                        mypair ((fst posl1)++(fst posl2)++(fst posl3)) ((snd posl1)++(snd posl2)++(snd posl3))
  | bver t01 t02 t03, bver t11 t12 t13 => let posl1 := destrEncMsg a r t01 t11 in
                                          let posl2 := destrEncMsg a r t02 t12 in
                                          let posl3 := destrEncMsg a r t03 t13 in
                                          mypair ((fst posl1)++(fst posl2)++(fst posl3)) ((snd posl1)++(snd posl2)++(snd posl3))
  | acc t01 t02 t03 t04, acc t11 t12 t13 t14 => let posl1 := destrEncMsg a r t01 t11 in
                                                let posl2 := destrEncMsg a r t02 t12 in
                                                let posl3 := destrEncMsg a r t03 t13 in
                                                let posl4 := destrEncMsg a r t04 t14 in
                                                mypair ((fst posl1)++(fst posl2)++(fst posl3)++(fst posl4)) ((snd posl1)++(snd posl2)++(snd posl3)++(snd posl4))
  | _, _ => mypair (cons (bol b1) nil) (cons (bol b2) nil)
  end
  with destrEncMsg (a r: nat) (t1 t2: message): prodOsl :=
  if message_beq t1 t2 then mypair [ ] [ ] else
         match t1, t2 with
         | comm t01 t02, comm t11 t12 =>  let posl1 := destrEncMsg a r t01 t11 in
                                          let posl2 := destrEncMsg a r t02 t12 in
                                          mypair ((fst posl1)++(fst posl2)) ((snd posl1)++(snd posl2))

         | open t01 t02 t03, open t11 t12 t13 => let posl1 := destrEncMsg a r t01 t11 in
                                                 let posl2 := destrEncMsg a r t02 t12 in
                                                 let posl3 := destrEncMsg a r t03 t13 in
                                                 mypair ((fst posl1)++(fst posl2)++(fst posl3)) ((snd posl1)++(snd posl2)++(snd posl3))
         | shufl t01 t02 t03, shufl t11 t12 t13 => let posl1 := destrEncMsg a r t01 t11 in
                                                   let posl2 := destrEncMsg a r t02 t12 in
                                                   let posl3 := destrEncMsg a r t03 t13 in
                                                   mypair ((fst posl1)++(fst posl2)++(fst posl3)) ((snd posl1)++(snd posl2)++(snd posl3))
         | enc t01 t02 t03, enc t11 t12 t13 => let posl1 := destrEncMsg a r t01 t11 in
                                               let posl2 := destrEncMsg a r t02 t12 in
                                               let posl3 := destrEncMsg a r t03 t13 in
                                               let res := mypair ((fst posl1)++(fst posl2)++(fst posl3)) ((snd posl1)++(snd posl2)++(snd posl3)) in
                                               let left := cons (msg (enc t01 t02 t03)) nil in
                                               let right := cons (msg (enc t11 t12 t13)) nil in
                                               (* match t02, t12 with
                                               | pi1 (ke (nonce n01)), pi1 (ke (nonce n11)) => if ((a =? n01)%nat &&(n01 =? n11)%nat)%bool then *)
                                               match t03, t13 with
                                                | re (nonce n02), re (nonce n12) => if ((r =? n02)%nat && (n02 =? n12)%nat)%bool then mypair left right else res
                                                |  _, _ => res
                                               end
                                                                                              (* (* else res
                                               | _, _ => res *)
                                               end *)

         | dec t01 t02, dec t11 t12 =>  let posl1 := destrEncMsg a r t01 t11 in
                                        let posl2 := destrEncMsg a r t02 t12 in
                                        let res :=  mypair ((fst posl1)++(fst posl2)) ((snd posl1)++(snd posl2)) in
                                        let left := (cons (msg (dec t01 t02)) nil) in
                                        let right := (cons (msg (dec t11 t12)) nil) in
                                        match t02, t12 with
                                        | pi2 (ke (nonce n1)), pi2 (ke (nonce n2)) => if ((a =? n1)%nat && (n1 =? n2)%nat)%bool
                                                                                      then mypair left right
                                                                                      else res
                                        | _, _ => res
                                        end

         | bsign t01 t02 t03, bsign t11 t12 t13 => let posl1 := destrEncMsg a r t01 t11 in
                                                   let posl2 := destrEncMsg a r t02 t12 in
                                                   let posl3 := destrEncMsg a r t03 t13 in
                                                   mypair ((fst posl1)++(fst posl2)++(fst posl3)) ((snd posl1)++(snd posl2)++(snd posl3))
         | bl t01 t02 t03, bl t11 t12 t13 => let posl1 := destrEncMsg a r t01 t11 in
                                             let posl2 := destrEncMsg a r t02 t12 in
                                             let posl3 := destrEncMsg a r t03 t13 in
                                             mypair ((fst posl1)++(fst posl2)++(fst posl3)) ((snd posl1)++(snd posl2)++(snd posl3))
         | sign t01 t02 t03, sign t11 t12 t13 => let posl1 := destrEncMsg a r t01 t11 in
                                                 let posl2 := destrEncMsg a r t02 t12 in
                                                 let posl3 := destrEncMsg a r t03 t13 in
                                                 mypair ((fst posl1)++(fst posl2)++(fst posl3)) ((snd posl1)++(snd posl2)++(snd posl3))
         | ub t01 t02 t03 t04, ub t11 t12 t13 t14 => let posl1 := destrEncMsg a r t01 t11 in
                                                     let posl2 := destrEncMsg a r t02 t12 in
                                                     let posl3 := destrEncMsg a r t03 t13 in
                                                     let posl4 := destrEncMsg a r t04 t14 in
                                                     mypair ((fst posl1)++(fst posl2)++(fst posl3)++(fst posl4)) ((snd posl1)++(snd posl2)++(snd posl3)++(snd posl4))
         | If b00 then t01 else t02, If b10 then t11 else t12 => let posl1 := destrEncBol a r b00 b10 in
                                                                 let posl2 := destrEncMsg a r t01 t11 in
                                                                 let posl3 := destrEncMsg a r t02 t12 in
                                                                 mypair ((fst posl1)++(fst posl2)++(fst posl3)) ((snd posl1)++(snd posl2)++(snd posl3))
| (t01, t02), (t11, t12) => let posl1 := destrEncMsg a r t01 t11 in
                            let posl2 := destrEncMsg a r t02 t12 in
                            mypair ((fst posl1)++(fst posl2)) ((snd posl1)++(snd posl2))
| (f l1), (f l2) => let res := (@destrEnc_f_all destrEncMsg a r l1 l2) in
                    let left := fst res in
                    let right := snd res in
                    mypair left right
      | pi1 t01, pi1 t11 => let posl1 := destrEncMsg a r t01 t11 in
                            mypair (fst posl1) (snd posl1)
      | pi2 t01, pi2 t11 => let posl1 := destrEncMsg a r t01 t11 in
                            mypair (fst posl1) (snd posl1)
         | _, _ => mypair (cons (msg t1) nil) (cons (msg t2) nil)
end.

Definition destrEncOs a r (os1 os2: oursum): prodOsl :=
  if oursum_beq os1 os2 then (mypair [ ] [ ]) else
  match os1, os2 with
  | msg t00, msg t10 => destrEncMsg a r t00 t10
  | bol b00, bol b10 => destrEncBol a r b00 b10
  | _, _ => mypair nil nil
  end.

Fixpoint destrEncOsl a r (l1 l2: oslist): prodOsl :=
  match l1, l2 with
  | h1::t1, h2::t2 => let rec:= destrEncOsl a r t1 t2 in
                      let curr:= destrEncOs a r h1 h2 in
                      let l00:= fst curr in
                      let l01:= fst rec in
                      let l10:= snd curr in
                      let l11:= snd rec in
                      (* let left:= noDup (l00 ++ l01) in
                      let right:= noDup (l10 ++ l11) in
                      mypair left right *)
                      (* remThenAppList l00 l10 l01 l11 *)
                      mypair ((fst curr)++(fst rec)) ((snd curr)++(snd rec))
  | _, _ => mypair [ ] [ ]
  end.
Axiom aplyCCA: forall {n} (l1 l2: mylist n) a r, let l1' := conv_mylist_listos l1 in
                                             let l2' := conv_mylist_listos l2 in
                                             let p := destrEncOsl a r l1' l2' in
                                             let y := oslToMylist (pi1ProdOsl p) (pi2ProdOsl p) in
                                             ((mylength y) =? 0 = false)%nat -> (pi1ProdMylist y) ~ (pi2ProdMylist y) -> l1 ~ l2.
Ltac aplyDestrEnc name seed :=
  match goal with
  |[|- ?X ~ ?Y] => apply aplyCCA with (l1:= X) (l2:=Y) (a:= name) (r:= seed); simpl; try auto
  end.



