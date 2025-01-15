(* Tepes and Pattern Matching in the Coq*)

Check true. (* Checking type of boolean expression true*)


Check true : B. (* Checking type of boolean expression true*)


(* Defining new types of Types*)
Inductive rgb : Type :=
    | red
    | green
    | blue.

Inductive colour : True :=
    | black
    | white
    | primary (p : rgb). (* defining black and white and third colour primary which takes p as argument of rgb type*)