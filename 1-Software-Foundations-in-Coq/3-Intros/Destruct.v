(* PROOF BY CASE ANALYSIS*)

(* We can use the destruct tactic to perform case analysis on a variable of an inductive type. *)
(* The simplest form of destruct is 'destruct term' which breaks down term according to its constructors. *)
(** In Coq, constructors are the building blocks of inductive types. They define how values of a type can be created. 
1. Boolean Type
Inductive bool : Type :=
  | true  : bool
  | false : bool.
Here true and false are the constructors of the bool type.

2. Natural Numbers
Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

*)

