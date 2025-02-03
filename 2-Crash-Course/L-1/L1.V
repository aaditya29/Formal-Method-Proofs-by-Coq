Inductive Bool := 
| true
| false.


Definition negb (b:Bool) : Bool :=
  match b with
  | true => false
  | false => true
  end.
  
  (* Testing our function*)
  Eval compute in (negb true).

  (* Starting proof of theorem*)
  (**
  1. Theorem negb_negb declares a new theorem named negb_negb
  2. negb (negb b) = b is the statement of the theorem. It asserts that if you apply the negb function (which negates a boolean value) twice to any boolean b, you will get back the original boolean b. *)
  Theorem negb_negb : forall (b : Bool), negb (negb b) = b.
  Proof.
    intros b. (*b is just an arbitrary value *)
    destruct b. (* We are doing case analysis on b *)
    + simpl. reflexivity. (* We are simplifying the goal and then using reflexivity to prove it *)
    +simple. reflexivity.
Qed.