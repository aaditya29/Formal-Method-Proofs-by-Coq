(* Lists in the comprehensive way*)

(*1. Definition of he list*)

Require Import Coq.Lists.List.
Import ListNotations.

Inductive list (A: Type) : Type :=
    | nil : list A
    | cons: A->list A->list A.
    