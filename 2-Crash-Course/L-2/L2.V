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
    +simpl. reflexivity.
Qed.


(*Defining another definition*)
Definition andb ( b1 b2 : Bool) : Bool :=
    match b1, b2 with
    | true, true => true
    | _, _ => false
    end.

(* Proof of returning statement when both are true else false*)
Theorem andb_true_both_arg_true : forall (b1 b2 : Bool),
    b1 = true -> b2 = true -> andb b1 b2 = true.
Proof.
    intros b1 b2 Hb1 Hb2.
    destruct b1.
    destruct b2.
    + simpl. reflexivity.
    + simpl. inversion Hb2.
    + destruct b2.
        ++ simpl. inversion Hb1.
        ++ simpl. inversion Hb1.
Qed.

Theorem andb_true_otherside : forall (b1 b2: Bool),
    andb  b1 b2 = true -> b1 = true /\ b2 = true.
Proof.
    intros b1 b2 Hb.
    destruct b1.
    destruct b2.
    split. reflexivity.
    reflexivity.
    inversion Hb.
    destruct b2.
    simpl in Hb.
    inversion Hb.
    simpl in Hb.
    inversion Hb.
Qed.

(* Proving AND is associative*)
Theorem andb_assoc : forall (b1 b2 b3 : Bool),
    andb b1 (andb b2 b3) = andb (andb b1 b2) b3.