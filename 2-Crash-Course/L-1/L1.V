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