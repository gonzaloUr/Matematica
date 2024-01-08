Set Implicit Arguments.

Section Seq.

Variable A : Type.

CoInductive Seq :=
  | Nil : Seq
  | Cons : A -> Seq -> Seq.

Definition hd (xs : Seq) :=
  match xs with
  | Nil => None
  | Cons x _ => Some x
  end.

Definition tl (xs : Seq) :=
  match xs with
  | Nil => None
  | Cons _ ys => Some ys
  end.

Fixpoint nth_tl (xs : Seq) (n : nat) :=
  match n with
  | 0 => Some xs
  | S m => 
    match tl xs with
    | None => None
    | Some ys => nth_tl ys m
    end
  end.

Definition nth (xs : Seq) (n : nat) :=
  match nth_tl xs n with
  | None => None
  | Some ys => hd ys
  end.

End Seq.
