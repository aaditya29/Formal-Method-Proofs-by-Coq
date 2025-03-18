(* LISTS IN COQ*)
(** Lists are one of the most fundamental data structures in Coq, representing sequences of elements of the same type. 
*)

(* Basic Definition And Syntax*)
Inductive natlist : Type := (* type of the list is the nat*)
  | nil (* list of empty type*)
  | cons (n : nat) (l : natlist). (* has a single value n of type nat and another pointer l of natlist type*)

Definition mylist := cons 1 (const 2 ( const 3 nil)). (* list of 3 elements*)


(* DEFINING A FUNCTION OF LIST*)

(*1. Counting copies of N*)
(* Here we are making a recursive function name repeat which takes two arguments n and count of nat type. Further the return type of natlist *)
Fixpoint repeat ( n count : nat) : natlist :=
  match count with
  | 0 => nil (* if count is 0 then it will return empty list*)
  | S count' => n :: (repeat n count') (* if count is some successor of S count' then it will return a list where n is added tot he result of recursively calling repeat with n and count'*)
  end.
Compute repeat 42 3.