(* LISTS IN COQ*)
(** Lists are one of the most fundamental data structures in Coq, representing sequences of elements of the same type. 
*)

(* Basic Definition And Syntax*)

Inductive list (A : Type) : Type :=
  | nil : list A
  | cons : A -> list A -> list A.