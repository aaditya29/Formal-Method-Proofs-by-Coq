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