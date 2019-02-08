
type bool =
| True
| False

type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val doChangeStatus : bool -> bool -> nat -> nat **)

let doChangeStatus b1 b2 n =
  match b1 with
  | True -> (match b2 with
             | True -> S n
             | False -> S (S n))
  | False -> (match b2 with
              | True -> S (S (S n))
              | False -> S (S (S (S n))))

(** val doUpdateFunction : bool list -> nat -> nat **)

let rec doUpdateFunction xs n =
  match xs with
  | Nil -> n
  | Cons (x1, xs') ->
    (match xs' with
     | Nil -> n
     | Cons (x2, _) -> doChangeStatus x1 x2 (doUpdateFunction xs' n))
