Section Vector.

    (* Argument A of type Type and returns nat of type Type*)
    Inductive Vector (A : Type) : nat -> Type := 
    (* Two ways to construct the two constructors*)
    | Nil : Vector A 0 (* Vector A of length 0 *)
    | Cons n : A  -> Vector A n -> Vector A (S n). (*Takes an element A of Vector type with length N and returns Vector A of length n+1 *)
