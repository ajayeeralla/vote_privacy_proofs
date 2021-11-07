Require Export prop_17.
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

Notation "'fst' p" := (pi1ProdOsl p) (at level 0): destr.

Definition pi2ProdOsl (p: prodOsl): oslist :=
  match p with
  | mypair l1 l2 => l2
  end.

Notation "'snd' p" := (pi2ProdOsl p) (at level 0): destr.

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

Open Scope destr.
 Fixpoint remove (t1 t2: oursum) (l1 l2: oslist): prodOsl :=
  match l1, l2 with
  | h1::tl1, h2::tl2 => if (h1 =?= t1) 
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
Check map.
Section all.
Variable f: message -> message -> prodOsl.
Fixpoint aply_att (l1 l2: list message): prodOsl :=
  match l1, l2 with
  | h1::t1, h2::t2 => let p:= f h1 h2 in
                      let rec:= aply_att t1 t2 in
                      mypair ((fst p)++(fst rec)) ((snd p)++(snd rec))
  | _, _ => mypair nil nil
  end.
End all. 
Open Scope msg_scope.
Fixpoint destrCommBol (b1 b2: Bool): prodOsl :=
  match b1, b2 with
  | eqb b01 b02, eqb b11 b12 => let posl1 := destrCommBol b01 b11 in
                                let posl2 := destrCommBol b02 b12 in
                                mypair ((fst posl1)++(fst posl2)) ((snd posl1)++(snd posl2))
  | eqm t01 t02, eqm t11 t12 =>  let posl1 := destrCommMsg t01 t11 in
                                 let posl2 := destrCommMsg t02 t12 in
                                 mypair ((fst posl1)++(fst posl2)) ((snd posl1)++(snd posl2))
  | ver t01 t02 t03, ver t11 t12 t13 => let posl1 := destrCommMsg t01 t11 in
                                        let posl2 := destrCommMsg t02 t12 in
                                        let posl3 := destrCommMsg t03 t13 in
                                        mypair ((fst posl1)++(fst posl2)++(fst posl3)) ((snd posl1)++(snd posl2)++(snd posl3))
  | bver t01 t02 t03, bver t11 t12 t13 => let posl1 := destrCommMsg t01 t11 in
                                          let posl2 := destrCommMsg t02 t12 in
                                          let posl3 := destrCommMsg t03 t13 in
                                          mypair ((fst posl1)++(fst posl2)++(fst posl3)) ((snd posl1)++(snd posl2)++(snd posl3))
  | acc t01 t02 t03 t04, acc t11 t12 t13 t14 => let posl1 := destrCommMsg t01 t11 in
                                                let posl2 := destrCommMsg t02 t12 in
                                                let posl3 := destrCommMsg t03 t13 in
                                                let posl4 := destrCommMsg t04 t14 in
                                                mypair ((fst posl1)++(fst posl2)++(fst posl3)++(fst posl4)) ((snd posl1)++(snd posl2)++(snd posl3)++(snd posl4))
  | _, _ => mypair (cons (bol b1) nil) (cons (bol b2) nil)
  end
  with destrCommMsg (t1 t2: message): prodOsl :=
         match t1, t2 with
         | open t01 t02 t03, open t11 t12 t13 => let posl1 := destrCommMsg t01 t11 in
                                                 let posl2 := destrCommMsg t02 t12 in
                                                 let posl3 := destrCommMsg t03 t13 in
                                                 mypair ((fst posl1)++(fst posl2)++(fst posl3)) ((snd posl1)++(snd posl2)++(snd posl3))
         | shufl t01 t02 t03, shufl t11 t12 t13 => let posl1 := destrCommMsg t01 t11 in
                                                   let posl2 := destrCommMsg t02 t12 in
                                                   let posl3 := destrCommMsg t03 t13 in
                                                   mypair ((fst posl1)++(fst posl2)++(fst posl3)) ((snd posl1)++(snd posl2)++(snd posl3))
         | enc t01 t02 t03, enc t11 t12 t13 => let posl1 := destrCommMsg t01 t11 in
                                               let posl2 := destrCommMsg t02 t12 in
                                               let posl3 := destrCommMsg t03 t13 in
                                               mypair ((fst posl1)++(fst posl2)++(fst posl3)) ((snd posl1)++(snd posl2)++(snd posl3))
         | dec t01 t02, dec t11 t12 =>  let posl1 := destrCommMsg t01 t11 in
                                        let posl2 := destrCommMsg t02 t12 in
                                        mypair ((fst posl1)++(fst posl2)) ((snd posl1)++(snd posl2))
         | bsign t01 t02 t03, bsign t11 t12 t13 => let posl1 := destrCommMsg t01 t11 in
                                                   let posl2 := destrCommMsg t02 t12 in
                                                   let posl3 := destrCommMsg t03 t13 in
                                                   mypair ((fst posl1)++(fst posl2)++(fst posl3)) ((snd posl1)++(snd posl2)++(snd posl3))
         | bl t01 t02 t03, bl t11 t12 t13 => let posl1 := destrCommMsg t01 t11 in
                                             let posl2 := destrCommMsg t02 t12 in
                                             let posl3 := destrCommMsg t03 t13 in
                                             mypair ((fst posl1)++(fst posl2)++(fst posl3)) ((snd posl1)++(snd posl2)++(snd posl3))
         | sign t01 t02 t03, sign t11 t12 t13 => let posl1 := destrCommMsg t01 t11 in
                                                 let posl2 := destrCommMsg t02 t12 in
                                                 let posl3 := destrCommMsg t03 t13 in
                                                 mypair ((fst posl1)++(fst posl2)++(fst posl3)) ((snd posl1)++(snd posl2)++(snd posl3))
         | ub t01 t02 t03 t04, ub t11 t12 t13 t14 => let posl1 := destrCommMsg t01 t11 in
                                                     let posl2 := destrCommMsg t02 t12 in
                                                     let posl3 := destrCommMsg t03 t13 in
                                                     let posl4 := destrCommMsg t04 t14 in
                                                     mypair ((fst posl1)++(fst posl2)++(fst posl3)++(fst posl4)) ((snd posl1)++(snd posl2)++(snd posl3)++(snd posl4))
         | If b00 then t01 else t02, If b10 then t11 else t12 => let posl1 := destrCommBol b00 b10 in
                                                                 let posl2 := destrCommMsg t01 t11 in
                                                                 let posl3 := destrCommMsg t02 t12 in
                                                                 mypair ((fst posl1)++(fst posl2)++(fst posl3)) ((snd posl1)++(snd posl2)++(snd posl3))
| (t01, t02), (t11, t12) => let posl1 := destrCommMsg t01 t11 in
                            let posl2 := destrCommMsg t02 t12 in
                            mypair ((fst posl1)++(fst posl2)) ((snd posl1)++(snd posl2))
| (f l1), (f l2) => let res := (@aply_att destrCommMsg l1 l2) in
                    let left := fst res in
                    let right := snd res in
                    mypair left right
         | _, _ => mypair (cons (msg t1) nil) (cons (msg t2) nil)
end.

Definition destrCommOs (os1 os2: oursum): prodOsl :=
  match os1, os2 with
  | msg t00, msg t10 => destrCommMsg t00 t10
  | bol b00, bol b10 => destrCommBol b00 b10
  | _, _ => mypair nil nil
  end.

Fixpoint destrCommOsl (l1 l2: oslist): prodOsl :=
  match l1, l2 with
  | h1::t1, h2::t2 => let rec:= destrCommOsl t1 t2 in
                      let curr:= destrCommOs h1 h2 in
                      let l00:= fst curr in
                      let l01:= fst rec in
                      let l10:= snd curr in
                      let l11:= snd rec in
                      remThenAppList l00 l10 l01 l11
                      (* mypair ((fst curr)++(fst rec)) ((snd curr)++(snd rec)) *)
  | _, _ => mypair nil nil
  end.
Axiom aply_funcapp: forall {n} (l1 l2: mylist n), let l1' := conv_mylist_listos l1 in
                                                  let l2' := conv_mylist_listos l2 in
                                                  let x := destrCommOsl l1' l2' in
                                                  let y := oslToMylist (pi1ProdOsl x) (pi2ProdOsl x) in
                                                  ((mylength y) =? 0 = false)%nat -> (pi1ProdMylist y) ~ (pi2ProdMylist y) -> l1 ~ l2.

