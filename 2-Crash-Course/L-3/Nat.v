Inductive Nat : Type :=
    | O : Nat
    | S : Nat -> Nat.
(** 0 => O
1 => S O
2 => S (S O) *)

Fixpoint add (n m: Nat) : Nat :=
    match n with
    | O => m
    | S n' => S ( add n' m) (* If n is some successor of a natural number n' then the function returns the successor of the result of recusrively calling add with n' and m.*)
    end.