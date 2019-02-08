
type bool =
| True
| False

type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k -> (match m with
            | O -> n
            | S l -> sub k l)

(** val unDoChangeStatus : bool -> bool -> nat -> nat **)

let unDoChangeStatus b1 b2 x =
  match b1 with
  | True ->
    (match b2 with
     | True -> sub x (S (S (S (S O))))
     | False -> sub x (S (S (S O))))
  | False -> (match b2 with
              | True -> sub x (S (S O))
              | False -> sub x (S O))

(** val unDoUpdateFunction : bool list -> nat -> nat **)

let rec unDoUpdateFunction xs n =
  match xs with
  | Nil -> n
  | Cons (x1, xs') ->
    (match xs' with
     | Nil -> n
     | Cons (x2, _) -> unDoChangeStatus x2 x1 (unDoUpdateFunction xs' n))
