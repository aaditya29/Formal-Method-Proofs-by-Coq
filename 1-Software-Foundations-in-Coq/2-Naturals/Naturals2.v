Module NatPlayground.
Definition minustwo (n : nat) : nat :=
    match n with
    | O => O (* if n is 0 then it returns 0*)
    | S O => O(* if n is successor of 0 then it returns 0*)
    | S (S n') => n'(* if n' is successor of successor of n then it returns n'*)
end.

Compute (minustwo 4).