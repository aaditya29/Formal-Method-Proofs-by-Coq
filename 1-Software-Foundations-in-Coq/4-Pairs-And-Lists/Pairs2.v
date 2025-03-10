Require Import List.
Import ListNotations.

(* Example 1: Function to swap the elements of a pair *)

Definition swap { A B: Type } (p : A * B) : B * A :=
  match p with
  | (a, b) => (b, a)
  end.

  Example swap_example :
    swap (1, false) = (false, 1).
Proof. reflexivity. Qed.
