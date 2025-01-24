(* Tepes and Pattern Matching in the Coq*)

Check true. (* Checking type of boolean expression true*)


Check true : B. (* Checking type of boolean expression true*)


(* Defining new types of Types*)
Inductive rgb : Type :=
    | red
    | green
    | blue.

Inductive colour : Type :=
    | black
    | white
    | primary (p : rgb). (* defining black and white and third colour primary which takes p as argument of rgb type*)


(* Defining functions on colours using the pattern matching*)
(*finding monochrome colour and finding if it is black or not*)
Definition monochrome (c : color) : bool :=
    match c with
    | black => true
    | white => true
    | primary p => false
    end.

(*finding if the colour is red or not using the pattern matching*)
Definition isred (c : color) : bool :=
    match c with
    | black => false
    | white => false
    | primary red => true
    | primary _ => false
    end.

