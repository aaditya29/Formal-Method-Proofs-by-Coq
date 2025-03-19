(* Defining a list*)

Require Import Coq.Lists.List.
Import ListNotations.

(** We define the list using Inductive keyword.
In Coq, the Inductive keyword is used to define inductive types. Inductive types are a fundamental concept in Coq, allowing you to define new data types by specifying their constructors. These types can be used to represent various kinds of data structures, such as natural numbers, lists, trees, and more. *)

Inductive list (A : Type) : Type :=
    | nil : list A
    | const : A -> list A -> list A. (* gere we are adding an element (head) to the list (tail) *)
 
(* In above example nil represents a list which is empty*)
(* cons h t reperesents a list where 
- h is the first element and t is the rest of the list*)

Compute (1 :: 2 :: 3 :: @Datatypes.nil nat).
(* here in output 1 is the head and 2,3 are tail*)



(* Extracting the head of a List*)

(* The hd function retreives the first element of a list with default value for empty lists*)

Fixpoint hd { A: Type } (default : A) (l: list A) : A :=
    match l with
    | nil => default
    | cons h _ => h
    end.