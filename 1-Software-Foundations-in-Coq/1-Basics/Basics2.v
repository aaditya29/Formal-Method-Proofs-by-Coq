(* Boolans in Coq*)

(**
The code defines an inductive type `bool` in Coq, which is similar to an enumeration in other programming languages.
- `Inductive bool: Type :=` declares a new inductive type named `bool`.
- `| true` and `| false` are the two possible values (constructors) of the `bool` type.
This is analogous to defining a boolean type with two possible values: true and false.
*)

Inductive bool: Type:=
| true
| false.

(*Definiing a new function in the boolean for giving output in negation*)
(** In `Definition negb (b:B) : B :=` the keyword definition is used to define a function or a constant in Coq.
    `negb` is the name of the function being defined.
    `b:B` b is the input parameter to the function. `:B` specifies that :b is the type of Boolean. In coq `B` defines type of booleans which can have only two values i.e. true or false
    `:B` specifies the return type of the function which is also a boolean B*)

(** `match b with ... end` uses a match expression to analyze the value of b and return the appropriate result.
    `match` keyword is used for pattern matching in Coq. Pattern matching allows us to "case-analyze" the possible values of a type.
    `b with` specifies that we are matching on the value of b.*)
Definition negb (b:B) : B :=
    match b with
    | true => false
    | false => true
    end.

(*Defining the function of logical AND*)
Definition andb (b1: B) (b2: B) : B :=
    match b1 with
    | true => b2
    | false => false
    end.

(*Defining the function of logical OR*)

Definition orb (b1: B) (b2: B) : B :=
    match b1 with
    | true => true(*If b1 is true, the function immediately returns true. *)
    | false => b2
    end.