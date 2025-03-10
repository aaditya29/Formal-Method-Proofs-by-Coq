# Understanding Pairs in Coq

Pairs are one of the fundamental data structures in Coq, allowing you to combine two values of potentially different types into a single composite value. Let me walk you through the syntax, usage, and some practical examples of pairs in Coq.

## Basic Syntax of Pairs

In Coq, a pair is defined using the `prod` type (product type), which is part of the standard library. Here's the essential syntax:

### Defining a Pair Type

```coq
Definition my_pair_type := prod nat bool.
(* Or equivalently: *)
Definition my_pair_type' := (nat * bool)%type.
```

### Creating Pair Values

```coq
Definition my_pair : nat * bool := (3, true).
Definition my_pair' := pair nat bool 3 true.  (* Explicit constructor *)
```

## Pair Constructor and Accessor Functions

The main constructor and functions for pairs are:

1. `pair`: The constructor for creating pairs

   ```coq
   Check pair.  (* forall A B : Type, A -> B -> A * B *)
   ```

2. `fst`: Extracts the first component

   ```coq
   Check fst.   (* forall A B : Type, A * B -> A *)
   ```

3. `snd`: Extracts the second component
   ```coq
   Check snd.   (* forall A B : Type, A * B -> B *)
   ```

## Pattern Matching with Pairs

You can use pattern matching to deconstruct pairs:

```coq
Definition swap {A B : Type} (p : A * B) : B * A :=
  match p with
  | (a, b) => (b, a)
  end.

(* Or equivalently using destructuring: *)
Definition swap' {A B : Type} (p : A * B) : B * A :=
  let (a, b) := p in (b, a).
```

## Example Programs with Pairs

Let's explore some useful functions that work with pairs:

```coq
Require Import List.
Import ListNotations.

(* Example 1: Function to swap the elements of a pair *)
Definition swap {A B : Type} (p : A * B) : B * A :=
  match p with
  | (a, b) => (b, a)
  end.

(* Example 2: Apply a function to each component of a pair *)
Definition map_pair {A B C D : Type}
                   (f : A -> C) (g : B -> D)
                   (p : A * B) : C * D :=
  match p with
  | (a, b) => (f a, g b)
  end.

(* Example 3: Zip two lists into a list of pairs *)
Fixpoint zip {A B : Type} (l1 : list A) (l2 : list B) : list (A * B) :=
  match l1, l2 with
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => (x, y) :: zip xs ys
  end.

(* Example 4: Unzip a list of pairs into a pair of lists *)
Fixpoint unzip {A B : Type} (l : list (A * B)) : (list A * list B) :=
  match l with
  | [] => ([], [])
  | (a, b) :: t =>
      let (l1, l2) := unzip t in
      (a :: l1, b :: l2)
  end.

(* Example 5: Calculating the Cartesian product of two lists *)
Fixpoint product {A B : Type} (l1 : list A) (l2 : list B) : list (A * B) :=
  match l1 with
  | [] => []
  | a :: t => map (fun b => (a, b)) l2 ++ product t l2
  end.

(* Now let's verify these functions with some examples *)

Example swap_example :
  swap (3, true) = (true, 3).
Proof. reflexivity. Qed.

Example map_pair_example :
  map_pair (fun n => n + 1) negb (5, true) = (6, false).
Proof. reflexivity. Qed.

Example zip_example :
  zip [1; 2; 3] ["a"; "b"; "c"] = [(1, "a"); (2, "b"); (3, "c")].
Proof. reflexivity. Qed.

Example unzip_example :
  unzip [(1, "a"); (2, "b"); (3, "c")] = ([1; 2; 3], ["a"; "b"; "c"]).
Proof. reflexivity. Qed.

Example product_example :
  product [1; 2] ["a"; "b"] = [(1, "a"); (1, "b"); (2, "a"); (2, "b")].
Proof. reflexivity. Qed.

(* Example 6: A more complex example - Merge sort using pairs *)
(* Split a list into two approximately equal parts *)
Fixpoint split {A : Type} (l : list A) : list A * list A :=
  match l with
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: t =>
      let (l1, l2) := split t in
      (x :: l1, y :: l2)
  end.

(* Merge two sorted lists *)
Fixpoint merge {A : Type} (cmp : A -> A -> bool) (l1 l2 : list A) : list A :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | x :: xs, y :: ys =>
      if cmp x y
      then x :: merge cmp xs (y :: ys)
      else y :: merge cmp (x :: xs) ys
  end.

(* Merge sort implementation *)
Fixpoint merge_sort {A : Type} (cmp : A -> A -> bool) (l : list A) : list A :=
  match l with
  | [] => []
  | [x] => [x]
  | _ =>
      let (l1, l2) := split l in
      merge cmp (merge_sort cmp l1) (merge_sort cmp l2)
  end.

Example merge_sort_example :
  merge_sort (fun n m => Nat.leb n m) [3; 1; 4; 1; 5; 9; 2; 6] =
  [1; 1; 2; 3; 4; 5; 6; 9].
Proof. reflexivity. Qed.

```

## Explanation of the Example Programs

Let me explain what each of these example functions does:

1. **`swap`**: Takes a pair and returns a new pair with the elements in reverse order. This demonstrates basic pattern matching on pairs.

2. **`map_pair`**: Applies two different functions to the respective components of a pair. This shows how to transform each element independently.

3. **`zip`**: Combines two lists into a single list of pairs, matching elements at the same positions. It stops when either list runs out of elements.

4. **`unzip`**: Does the opposite of `zip` - it takes a list of pairs and returns a pair of lists. This function uses recursion and pattern matching on both lists and pairs.

5. **`product`**: Computes the Cartesian product of two lists, creating pairs of all possible combinations of elements from the two lists.

6. **`merge_sort`**: A more complex example that uses pairs to implement the merge sort algorithm:
   - `split` divides a list into two approximately equal parts (using a pair to hold both parts)
   - `merge` combines two sorted lists into one
   - `merge_sort` recursively sorts the list using divide-and-conquer

## Dependent Pairs (Sigma Types)

For more advanced usage, Coq also offers dependent pairs, also known as Sigma types, where the type of the second component may depend on the value of the first component:

```coq
(* A dependent pair - the second component's type depends on the first *)
Definition dependent_pair_example :=
  existT (fun n:nat => Vector.t bool n) 3 (Vector.cons bool true 2 (Vector.cons bool false 1 (Vector.cons bool true 0 (Vector.nil bool)))).
```

## Key Takeaways

1. Pairs in Coq let you combine two values, potentially of different types.
2. You can create pairs using the `pair` constructor or the `(a, b)` notation.
3. Extract components using `fst`, `snd`, or pattern matching.
4. Pairs are fundamental for many algorithms and data structures, especially those involving relationship between two elements.
5. More complex data structures like trees, graphs, and maps often use pairs as building blocks.
