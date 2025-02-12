(* MODULES IN COQ*)
(** 
    # Modules in Coq

    Modules in Coq are used to structure and organize code. They allow us to group related definitions, theorems, and proofs together, making our code more modular and easier to manage. Modules can be nested, and we can control the visibility of the contents of a module using the `Export`, `Import`, and `Include` commands.

    ## Basic Module Syntax

    A module is defined using the `Module` keyword followed by the module name and a block of code. Here is a simple example:

    You can access the contents of a module using the dot notation:

    ```coq
    Check MyModule.x.  (* MyModule.x : nat *)
    Check MyModule.y.  (* MyModule.y : nat *)
    ```

    ## Importing and Exporting

    - `Import`: Brings the contents of a module into the current scope, allowing you to use them without the module prefix.
    - `Export`: Makes the contents of a module available to any module that imports the current module.
    - `Include`: Includes the contents of a module into the current module, effectively copying them.

    Example:

    ```coq
    Module A.
        Definition a := 1.
    End A.

    Module B.
        Import A.
        Definition b := a + 1.
    End B.

    Module C.
        Export A.
        Definition c := a + 2.
    End C.

    Module D.
        Include A.
        Definition d := a + 3.
    End D.
    ```

    In this example:
    - `B` can use `a` directly because it imports `A`.
    - Any module that imports `C` will also have access to `a` because `C` exports `A`.
    - `D` includes `A`, so `a` is directly part of `D`.

    ## Parameterized Modules (Functors)

    Coq also supports parameterized modules, known as functors. A functor is a module that takes other modules as parameters. This allows for more flexible and reusable code.

    Example:

    ```coq
    Module Type XType.
        Parameter x : nat.
    End XType.

    Module Functor (X : XType).
        Definition y := X.x + 1.
    End Functor.

    Module Instance.
        Definition x := 42.
    End Instance.

    Module Result := Functor(Instance).
    ```

    In this example, `Functor` is a parameterized module that takes a module of type `XType` and defines `y` based on `X.x`. `Result` is an instance of `Functor` with `Instance` as its parameter.
*)
Module Playground.
    Inductive rgb := red | green | blue.
    Definition b : rgb := blue.
End Playground.

Inductive B := trueB | falseB.

Definition b: B := trueB.

Check Playground.b : Playground.rgb.
Check b: B.

(* NUMBERS*)
Module NatPlayground.

Inductive N: Type :=
    | O (* O is the predecessor*)
    | S (n : N). (* S means successor of N*)
(* In above definition, 0 is represented by [0], 1 by [S 0], 2 by [S (S 0)], and so on.*)

Definition pred (n : N) : N :=
    match n with
    | O => O(* predecessor of 0 is 0*)
    | S n' => n' (* predecessor of S n' is n'*)
    end.
End NatPlayground.

Check (S (S (S O))).