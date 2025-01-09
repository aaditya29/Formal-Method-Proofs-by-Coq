
(*Explanation of the following code*)

(*1. Inductive day: Type :=*)
(** `Inductive` keyword is used to define a new inductive data type. An inductive data type is one that is built by specifying all its possible values explicitly. `day` is the name of data type we are defining*)
(** `Type` specifies that day is a type in Coq. Coq uses a type system to classify expressions, and Type is the kind used to define datatypes like numbers, booleans, or user-defined types like this.*)
  
  (*2. | monday*)
  (** `|` is used to separate the different constructors of the inductive type. `monday` is the first constructor of the inductive type `day`.*)
  
  (*3. | tuesday*)
  (** `tuesday` is the second constructor of the inductive type `day`.*)
  
  (*4. | wednesday*)
  (** `wednesday` is the third constructor of the inductive type `day`.*)
  
  (*5. | thursday*)
  (** `thursday` is the fourth constructor of the inductive type `day`.*)
  
  (*6. | friday*)
  (** `friday` is the fifth constructor of the inductive type `day`.*)
  
  (*7. | saturday*)
  (** `saturday` is the sixth constructor of the inductive type `day`.*)
  
  (*8. | sunday.*)
  (** `sunday` is the seventh constructor of the inductive type `day`.*)
  
  (*The below code defines a new inductive data type `day` with seven constructors `monday`, `tuesday`, `wednesday`, `thursday`, `friday`, `saturday`, and `sunday`. Each constructor represents a day of the week.*)
  
Inductive day: Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

  (*Creating a function on days*)
  
  (** 
    The [next_weekday] function takes a day of the week [d] as input and returns the next weekday.
    - If the input is [monday], it returns [tuesday].
    - If the input is [tuesday], it returns [wednesday].
    - If the input is [wednesday], it returns [thursday].
    - If the input is [thursday], it returns [friday].
    - If the input is [friday], it returns [monday].
    - If the input is [saturday] or [sunday], it returns [monday].
  *)

  Definition next_weekday (d:day) : day :=
    match d with
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday => monday
    | saturday => monday
    | sunday => monday
    end.

(*Using the above function*)
Compute (next_weekday monday).
(*Output: monday : day*)

(*Now we can check what we are expecting our result to be in the form of a Coq example*)
Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

(* We are now giving a proof for giving evidence to our claim *)
Proof. simpl. reflexivity. Qed.