Require Import Coq.Unicode.Utf8.
Require Import Zf.

Lemma empty_set_equiv : ∀ a, a <> ∅ <-> ∃ x, x ∈ a.
Proof.
  intros.
  split.
  - intros.
    assert (a <> ∅ <-> ¬ (∀ x, x ∈ a ↔ x ∈ ∅)).
    apply not_iff_compat.
    apply extension.
    assert (¬ (∀ x, x ∈ a ↔ x ∈ ∅)).
    apply H0.
    assumption.
Abort.

Lemma intersection_of_equiv : ∀ a x, a <> ∅ -> (x ∈ (intersection_of a) <-> ∀ y, y ∈ a -> x ∈ y).
Proof.
Abort.

Lemma demorgan_intersection : ∀ u a b, u - (a ∩ b) = (u - a) ∪ (u - b).
Proof.
  intros.
  apply extension.
  intros.
  split.
  - intros.
    assert (x ∈ u ∧ ¬ x ∈ (a ∩ b)).
    apply (specification_belongs u (λ x, ¬ x ∈ (a ∩ b)) x).
    assumption.
    elim H0. 
    intros.
Abort.

Lemma complement_idem : ∀ u a, a ⊆ u -> u - (u - a) = a.
Proof.
  intros.
  apply extension.
  intros.
  split.
  - intros.
Abort.

Lemma complement_union : ∀ u a, a ⊆ u -> a ∪ (u - a) = u. 
Proof.
  intros.
  apply extension.
  intros.
  split.
  - intros.
    assert (x ∈ a ∨ x ∈ (u - a)).
    apply union_op_equiv.
    assumption.
    elim H1.
    * intros.
      unfold "⊆" in H.
      apply H.
      assumption.
    * intros.
      assert (x ∈ u ∧ ¬ x ∈ a).
      apply complement_equiv.
      assumption.
      exact (proj1 H3).
  - intros.
    apply union_op_equiv.
    right.
Abort.

Lemma complement_subset : ∀ u a b, a ⊆ u -> b ⊆ u -> (a ⊆ b <-> (u - b) ⊆ (u - a)).
Proof.
  intros.
  split.
  - intros.
    unfold "⊆".
    intros.
Abort.
