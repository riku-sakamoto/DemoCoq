
type bool =
| True
| False

type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

val sub : nat -> nat -> nat

val unDoChangeStatus : bool -> bool -> nat -> nat

val unDoUpdateFunction : bool list -> nat -> nat
