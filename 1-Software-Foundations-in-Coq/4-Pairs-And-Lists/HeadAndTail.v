(* Defining a list*)

(** We define the list using Inductive keyword.
In Coq, the Inductive keyword is used to define inductive types. Inductive types are a fundamental concept in Coq, allowing you to define new data types by specifying their constructors. These types can be used to represent various kinds of data structures, such as natural numbers, lists, trees, and more. *)

Inductive list (A : Type) : Type :=
    | nil : list A
    | const : A -> list A -> list A. (* gere we are adding an element (head) to the list (tail) *)
 
(* In above example nil represents a list which is empty*)
(* cons h t reperesents a list where 
- h is the first element and t is the rest of the list*)

