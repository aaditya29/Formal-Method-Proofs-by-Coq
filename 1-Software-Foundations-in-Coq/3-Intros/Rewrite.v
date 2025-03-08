(* Proof By Rewriting*)

Theorem plus_id_example : forall n m:nat,
    n = m ->
    n+n = m + m. (* proving that if two numbers are same then adding them is also same *)

Proof.
    intros n m. (* moving both quantifiers into the context*)
    intros H. (*moving the hypothesis into the context*)
    rewrite -> H. (*rewriting the goal*)
    reflexivity.
Qed.