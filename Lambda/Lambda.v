Module Type LambdaSig.
  Inductive Term :=
    | atom : nat -> Term
    | apply : Term -> Term -> Term
    | abstract : nat -> Term -> Term.
End LambdaSig.

