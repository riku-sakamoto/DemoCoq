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

(*任意数のリストに対するReDo-UnDoを証明*)


(*Redo関数*)
  (*2組に対する評価：単独Do関数*)
Definition DoChangeStatus(b1 b2:bool)(n:nat):nat :=
 match (b1, b2) with
 | (true, true) => S n 
 | (true, false) => S (S n)
 | (false, true) => S (S (S n))
 | (false, false) => S (S (S (S n)))
 end.

  (*任意数のリストに対する評価*)
Fixpoint DoUpdateFunction (xs:list bool)(n:nat):nat :=
 match xs with
 | nil => n
 | x1::xs' => match xs' with
             | nil => n
             | x2::xs'' => DoChangeStatus x1 x2 (DoUpdateFunction xs' n)
             end
 end.

(*UnDo関数*)
  (*2組に対する評価：単独UnDo関数*)
Definition UnDoChangeStatus(b1 b2:bool)(x:nat):nat :=
 match (b1, b2) with
 | (true, true) => x - 4
 | (true, false) => x - 3
 | (false, true) => x - 2
 | (false, false) => x - 1
 end.

  (*任意数のリストに対する評価*)
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

  (*boolの反転を定義*)
Definition rev_bool (a:bool):bool :=
  match a with
  |true => false
  |false => true
 end.

  (*順番も正負も逆なboolリストを定義*)
Fixpoint rev_bool_list (l:list bool):list bool :=
  match l with 
  | nil => nil
  | x::xs => rev_bool_list xs ++ [rev_bool x]
  end.


(* 単独Do関数に対する交換法則を証明 *)
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


(* 単独Do関数 -> 単独ReDo関数によってもとに戻ることを確認 *)
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


(* 反転リストに対する分配則を証明 *)
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

(* 反転リストに対する結合則を証明 *)
Theorem unify_rev_bool_list:forall (l:list bool)(a:bool),
  rev_bool_list(l)++[rev_bool a] = rev_bool_list(a::l).

Proof.
intros.
simpl.
reflexivity.
Qed.



(* Undo関数に対する、リストを前から分配する分配則を証明 *)
 Theorem DecompositionUnDo : forall (l:list bool)(a:bool)(b:bool)(n:nat),
  UnDoUpdateFunction (a::b::l) n =  UnDoChangeStatus b a (UnDoUpdateFunction (b::l) n).

Proof.
intros.
simpl.
reflexivity.

Qed.

(* Undo関数に対する、リストを後から分配する分配則を証明 *)
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


(* do関数に対する、リストを前から分配する分配則を証明 *)
 Theorem DecompositionDo : forall (l:list bool)(a:bool)(b:bool)(n:nat),
  DoUpdateFunction (a::b::l) n =  DoChangeStatus a b (DoUpdateFunction (b::l) n).

Proof.
intros.
simpl.
reflexivity.

Qed.


(* Main *)
(* 任意数のリストに対してReDoしてUnDoしたら元の数に戻ることを証明 *)
Theorem ReDoUnDoFunction : forall (xs:list bool) (n:nat), 
  UnDoUpdateFunction (rev_bool_list xs) (DoUpdateFunction xs n) = n.

Proof.
intros.
induction xs. (*リストに対する帰納法を使う*)
simpl.
reflexivity.

intros.
induction xs.
simpl.
reflexivity.

intros.
rewrite decomposition_rev_bool_list. (*既に証明した定理を用いる*)
rewrite DecompositionDo.
rewrite DecompositionUnDo2.
rewrite ReDoUnDo.
rewrite unify_rev_bool_list.
rewrite IHxs. (*帰納法の仮定を使用*)
reflexivity.
Qed.



Require Extraction.
Extraction Language OCaml.
Extraction "C:\CoqSample\ForDemo\DoUpdateFunction.ml" DoUpdateFunction.
Extraction "C:\CoqSample\ForDemo\UnDoUpdateFunction.ml" UnDoUpdateFunction.

