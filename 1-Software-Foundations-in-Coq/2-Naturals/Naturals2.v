Module NatPlayground.
Definition minustwo (n : nat) : nat :=
    match n with
    | O => O (* if n is 0 then it returns 0*)
    | S O => O(* if n is successor of 0 then it returns 0*)
    | S (S n') => n'(* if n' is successor of successor of n then it returns n'*)
end.

Compute (minustwo 4).

(**Recursive functions are defined using the [FIXPOINT] keyword. It is a venacular command*)
Fixpoint even(n: nat) : B :=
    match n with
    | O => true
    | S O => false
    | S (S n') => even n'
end.

(*Defining odd in the same way*)
Definition odd(n:nat) : Bool :=
    negb (even n).


(* Adding two numbers*)
Fixpoint plus (n m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
end.

(* Multiplying two numbers*)
Fixpoint mul (m n: nat) : nat :=
    match n with
    | O => O
    | S n' => plus m (mul m n')
    end.

