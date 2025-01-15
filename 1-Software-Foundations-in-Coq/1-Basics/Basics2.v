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
Definition negb (b:B) : B := (*negb is a function with argument b of type Bool and output of function is going to be Bool*)
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
    end. (*If b1 is false, the function returns the value of b2.*)

(*Writing the proof*)

(* Here we are defining series of unit tests for the orb function (logical OR) that was previously defined.*)

(*Here example is used to define a test case with test_orb1 as the name of the test case.*)
(* `orb true false = true` is the statement we want to prove. It asserts that the result of orb true false (logical OR of true and false) is equal to true.*)
(* Proof. begins the proof for the test case and `simpl` simplifies the expression by reducing it to its simplest form using the definition of orb.*)
(* Here Coq will replace (orb true false) with true (based on the definition of orb).*)
Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. relfexivity. Qed. 



(* Writing new symbolic notations for the existing definitions. *)
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

(* Examples using the new notations *)
Example test_andb1: (true && false) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb2: (true && true) = true.
Proof. simpl. reflexivity. Qed.
Example test_negb1: (~~ true) = false.
Proof. simpl. reflexivity. Qed.
Example test_negb2: (~~ false) = true.
Proof. simpl. reflexivity. Qed.

(* Writing above function with the if expressions*)
Definition negb (b:B) : B := (* Defining function negb with argument b and Boolean type which returns the Boolean*)
    if b then false
    else true.

Definition andb (b1:B) (b2:B): B :=
    if b1 then b2
    else false.
    
