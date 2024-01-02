Require Import Coq.Unicode.Utf8.

Class Lambda (A : Type) := {
  atom : nat -> A;
  apply : A -> A -> A;
  abstract : nat -> A -> A;
  complete : ∀ t : A, (∃ n : nat, t = atom n) ∨ (∃ m n : A, t = apply m n) ∨ (∃ (n : nat) (m : A), t = abstract n m);
}.

