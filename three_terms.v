(*
Listの書き方
ListNoatations不使用時　List = (1::2::3::nil)
ListNoatations使用時　List = [1;2;3]
*)


Require Import Arith.
Require Import List.
Require Export Bool.
Import ListNotations.

(*Redo関数*)
Definition DoChangeStatus(b1 b2:bool)(n:nat):nat :=
 match (b1, b2) with
 | (true, true) => S n 
 | (true, false) => S (S n)
 | (false, true) => S (S (S n))
 | (false, false) => S (S (S (S n)))
 end.

(* 3つの入力に対してReDo関数を実行 *)
Fixpoint DoUpdateFunction (b1 b2 b3: bool)(n:nat):nat :=
 DoChangeStatus b1 b2 (DoChangeStatus b2 b3 n). 



(*UnDo関数*)
Definition UnDoChangeStatus(b1 b2:bool)(x:nat):nat :=
 match (b1, b2) with
 | (true, true) => x - 4
 | (true, false) => x - 3
 | (false, true) => x - 2
 | (false, false) => x - 1
 end.

(* 3つの入力に対してUnDo関数を実行 *)
Fixpoint UnDoUpdateFunction (b1 b2 b3 :bool)(n:nat):nat :=
 UnDoChangeStatus b2 b1 (UnDoChangeStatus b3 b2 n). 

(* 試しに計算 *)
Compute DoUpdateFunction true true false 3.
Compute UnDoUpdateFunction true false false 6.

(*Boolを反転させる*)
Definition rev_bool (a:bool):bool :=
  match a with
  |true => false
  |false => true
 end.

(* 小定理 1 *)
(* ReDo(n+1) = ReDo(n) + 1 *)
Theorem DoSn : forall (a b:bool) (n:nat), 
  DoChangeStatus a b (S n) =  S (DoChangeStatus a b n).

(* 方針：a,b2つのBool値について地道に場合分け *)

Proof.
intros.
case a. (* aについて地道に場合分け *)

(* a=true の時*)
case b. (* bについて地道に場合分け *)
-
(* b=true の時*)
intros.
simpl.
induction n. (* nに関する帰納法*)
(* n=nil の時*)
simpl.
reflexivity.

(* 一般nの時*)
simpl.
reflexivity.
-
(* a=falseの時 *)
(* a=後は同様 *)
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

(* 小定理 2 *)
(* Undo(ReDo(n)) = n *)
Theorem ReDoUnDo : forall (a b:bool) (n:nat), 
  UnDoChangeStatus (rev_bool a) (rev_bool b) (DoChangeStatus a b n) = n.

Proof.
intros.
case a.
case b.
simpl.

(* nに関する帰納法*)
induction n.
-
simpl.
auto.
-
(* n=n+1の時 *)
(*小定理１を使って式を分解*)
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

(* 小定理 3 *)
(* Undo(a b c n) = UnDoChangeStatus a b UnDoChangeStatus(b c n) *)
Theorem DecompositionUnDo : forall (a b c:bool) (n:nat),
  UnDoUpdateFunction a b c n =  UnDoChangeStatus b a (UnDoChangeStatus c b n).

Proof.
intros.
case a.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

(* 小定理 4 *)
(* Do(a b c n) = DoChangeStatus a b DoChangeStatus(b c n) *)
Theorem DecompositionDo : forall (a b c:bool) (n:nat),
  DoUpdateFunction a b c n =  DoChangeStatus a b (DoChangeStatus b c n).

Proof.
intros.
case a.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.


Theorem ReDoUnDoFunction : forall (a b c:bool) (n:nat), 
  UnDoUpdateFunction (rev_bool c) (rev_bool b) (rev_bool a) (DoUpdateFunction a b c n) = n.

Proof.
intros.
(* 小定理3より、UnDoUpdateFunctionを展開 *)
rewrite DecompositionUnDo.
(* 小定理4より、DoUpdateFunctionを展開 *)
rewrite DecompositionDo.
(* 小定理2より、DoしてUnDoしたら元に戻る *)
rewrite ReDoUnDo.
rewrite ReDoUnDo.
reflexivity.
Qed.
