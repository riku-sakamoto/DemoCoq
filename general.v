Require Import Arith.
Require Import List.
Require Export Bool.
Import ListNotations.
Require Import Wf_nat.

(*
Listの書き方
ListNoatations不使用時　List = (1::2::3::nil)
ListNoatations使用時　List = [1;2;3]
*)


(*Redo関数*)
Definition DoChangeStatus(b1 b2:bool)(n:nat):nat :=
 match (b1, b2) with
 | (true, true) => S n 
 | (true, false) => S (S n)
 | (false, true) => S (S (S n))
 | (false, false) => S (S (S (S n)))
 end.

Fixpoint DoUpdateFunction (xs:list bool)(n:nat):nat :=
 match xs with
 | nil => n
 | x1::xs' => match xs' with
             | nil => n
             | x2::xs'' => DoChangeStatus x1 x2 (DoUpdateFunction xs' n)
             end
 end.

(*UnDo関数*)
Definition UnDoChangeStatus(b1 b2:bool)(x:nat):nat :=
 match (b1, b2) with
 | (true, true) => x - 4
 | (true, false) => x - 3
 | (false, true) => x - 2
 | (false, false) => x - 1
 end.


Fixpoint UnDoUpdateFunction (xs:list bool)(n:nat):nat :=
 match xs with
 | nil => n
 | x1::xs' => match xs' with
             | nil => n
             | x2::xs'' => UnDoChangeStatus x2 x1 (UnDoUpdateFunction xs' n)
             end
 end.


Compute DoUpdateFunction (true :: true :: false :: nil) 3.
Compute UnDoUpdateFunction (true :: false :: false :: nil) 6.

Definition rev_bool (a:bool):bool :=
  match a with
  |true => false
  |false => true
 end.


Theorem DoSn : forall (a b:bool) (n:nat), 
  DoChangeStatus a b (S n) =  S (DoChangeStatus a b n).

Proof.
intros.
case a.
case b.
-
intros.
simpl.
induction n.
simpl.
reflexivity.

simpl.
reflexivity.
-
intros.
simpl.
induction n.
simpl.
reflexivity.
reflexivity.

-
case b.
intros.
simpl.
induction n.
simpl.
reflexivity.

reflexivity.

intros.
simpl.
induction n.
simpl.
reflexivity.

reflexivity.
Qed.


Theorem ReDoUnDo : forall (a b:bool) (n:nat), 
  UnDoChangeStatus (rev_bool a) (rev_bool b) (DoChangeStatus a b n) = n.

Proof.
intros.
case a.
case b.
simpl.

induction n.
-
simpl.
auto.
-
rewrite DoSn.
simpl.
auto.
-
induction n.
simpl.
auto.

simpl.
rewrite DoSn.
auto.

-
case b.
induction n.
simpl.
auto.

simpl.
rewrite DoSn.
auto.

induction n.
simpl.
auto.

simpl.
rewrite DoSn.
auto.
Qed.

Fixpoint rev_bool_list (l:list bool):list bool :=
  match l with 
  | nil => nil
  | x::xs => rev_bool_list xs ++ [rev_bool x]
  end.

Theorem decomposition_rev_bool_list:forall (l:list bool)(a:bool)(b:bool),
  rev_bool_list(a::b::l) = rev_bool_list(l)++[rev_bool b]++[rev_bool a].

Proof.
intros.
simpl.
SearchRewrite(_++_++_).
rewrite app_assoc_reverse.
SearchRewrite(_++_).
reflexivity.
Qed.

Theorem unify_rev_bool_list:forall (l:list bool)(a:bool),
  rev_bool_list(l)++[rev_bool a] = rev_bool_list(a::l).

Proof.
intros.
simpl.
reflexivity.
Qed.



(* 小定理 3 *)
(* Undo(a b c n) = UnDoChangeStatus a b UnDoChangeStatus(b c n) *)
 Theorem DecompositionUnDo : forall (l:list bool)(a:bool)(b:bool)(n:nat),
  UnDoUpdateFunction (a::b::l) n =  UnDoChangeStatus b a (UnDoUpdateFunction (b::l) n).

Proof.
intros.
simpl.
reflexivity.

Qed.

Theorem DecompositionUnDo2 : forall (l:list bool)(a:bool)(b:bool)(n:nat),
  UnDoUpdateFunction (l++[b]++[a]) n =  UnDoUpdateFunction (l++[b]) (UnDoChangeStatus a b n).

Proof.
intros.
induction l.
simpl.
reflexivity.
induction l.
simpl.
reflexivity.
case a0.
simpl.
apply f_equal_nat. (*繰り返し適用*)
assumption. (*仮定の適用。「nを仮定した」という事実そのものを指している？？*)
(* info_auto. *) (*autoの中身を見る*)
simpl.
apply f_equal_nat.
assumption.
Qed.


(* 小定理 3 *)
(* Undo(a b c n) = UnDoChangeStatus a b UnDoChangeStatus(b c n) *)
 Theorem DecompositionDo : forall (l:list bool)(a:bool)(b:bool)(n:nat),
  DoUpdateFunction (a::b::l) n =  DoChangeStatus a b (DoUpdateFunction (b::l) n).

Proof.
intros.
simpl.
reflexivity.

Qed.



Theorem ReDoUnDoFunction : forall (xs:list bool) (n:nat), 
  UnDoUpdateFunction (rev_bool_list xs) (DoUpdateFunction xs n) = n.

(*帰納法の仮定がIHhoge(hogeは変数名)の形で追加*)
Proof.
intros.
induction xs.
simpl.
reflexivity.

intros.
induction xs.
simpl.
reflexivity.

intros.
rewrite decomposition_rev_bool_list.
rewrite DecompositionDo.

SearchRewrite(_++_).
rewrite DecompositionUnDo2.
rewrite ReDoUnDo.
rewrite unify_rev_bool_list.
rewrite IHxs.
reflexivity.
Qed.
