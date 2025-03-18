(* LISTS IN COQ*)
(** Lists are one of the most fundamental data structures in Coq, representing sequences of elements of the same type. 
*)

(* Basic Definition And Syntax*)
Inductive natlist : Type := (* type of the list is the nat*)
  | nil (* list of empty type*)
  | cons (n : nat) (l : natlist). (* has a single value n of type nat and another pointer l of natlist type*)

Definition mylist := cons 1 (const 2 ( const 3 nil)). (* list of 3 elements*)

