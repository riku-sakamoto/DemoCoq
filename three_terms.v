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


Fixpoint UnDoUpdateFunction (b1 b2 b3 :bool)(n:nat):nat :=
 UnDoChangeStatus b2 b1 (UnDoChangeStatus b3 b2 n). 


Compute DoUpdateFunction true true false 3.
Compute UnDoUpdateFunction true false false 6.

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
rewrite DecompositionUnDo.
rewrite DecompositionDo.
rewrite ReDoUnDo.
rewrite ReDoUnDo.
reflexivity.
Qed.
