
type bool =
| True
| False

type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

val doChangeStatus : bool -> bool -> nat -> nat

val doUpdateFunction : bool list -> nat -> nat
