(** In Coq, pairs are a way to group two values together. They are also known as tuples or Cartesian products. Here's a basic explanation and example of how pairs work in Coq.
Creating Pairs
You can create a pair using the pair constructor or simply by using the notation (x, y).

Accessing Elements of a Pair
To access the elements of a pair, you use the fst and snd functions, which return the first and second elements of the pair, respectively. *)

(* Defining a Pair Type*)
Definition my_pair_type := prod nat bool.
(* Equivalently*)
Definition my_pair_type' := (nat * bool)%type.

(*Creating Pair Values*)
Definition my_pair : nat * bool := (3, true).
Definition my_pair' := pair nat bool 3 true. (* Explicit way to define constructor*)