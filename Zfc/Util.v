Require Import Coq.Unicode.Utf8.

Section Logic.

Variable T : Type.
Variable P : T -> Prop.

Lemma neg_forall : ¬ (∀ x, P x) <-> ∃ x, ¬ P x.
Proof.
  split.
Qed.

End Logic.