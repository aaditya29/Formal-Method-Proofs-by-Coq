(* Comparing equality of function and returning boolean*)
Fixpoint eqb (n m : nat) : bool :=
    match n with
    | O => match m with
            | O => true
            | S m' => false
            end
    |S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
end.

(* leb function tests whether its first argument is less than or  equal to its second argument*)
Fixpoint leb (m n: nat) : bool :=
    match n with
    | O => true
    | S n' =>
        match m with
        | O => true
        | S m' => leb n' m'
        end
    end.