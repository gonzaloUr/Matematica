Require Import Coq.Unicode.Utf8.
Require Import Coq.Init.Logic.

Declare Scope set_scope.
Open Scope set_scope.

Axiom set : Type.

Axiom belongs : set -> set -> Prop.
Notation "A ∈ B" := (belongs A B) (at level 70, B at level 0) : set_scope.

Definition subset a b := ∀ x, x ∈ a -> x ∈ b.
Notation "A ⊆ B" := (subset A B) (at level 70, B at level 0) : set_scope.

Axiom extension : ∀ a b, a = b ↔ ∀ x, x ∈ a ↔ x ∈ b.

Lemma extension_equiv : ∀ a b, a = b <-> a ⊆ b ∧ b ⊆ a.
Proof.
  intros.
  split.
  - intros.
    unfold subset.
    + cut (a = b <-> ∀ x, x ∈ a <-> x ∈ b).
      * intros.
        split.
        -- apply extension.
           symmetry.
           assumption.
        -- apply extension.
           assumption.
      * apply extension.
  - intros.
    elim H.
    intros.
    unfold "⊆" in H0, H1.
    + cut (∀ x, x ∈ a <-> x ∈ b).
      * intros.
        apply extension.
        assumption.
      * intros.
        split.
        -- apply H0.
        -- apply H1.
Qed.

Axiom exists_empty_set : { a | ∀ b, ¬ b ∈ a }.

Definition empty_set := proj1_sig exists_empty_set.
Notation "∅" := empty_set (at level 0) : set_scope.

Axiom specification : ∀ a P, { b | ∀ x, x ∈ b <-> x ∈ a ∧ P x }.

Lemma specification_belongs : ∀ a P x, x ∈ (proj1_sig (specification a P)) <-> x ∈ a ∧ P x.
Proof.
  intros.
  split.
  all : intros; apply (proj2_sig (specification a P)); assumption.
Qed.

Lemma all_superset_empty_set : ∀ a, ∅ ⊆ a.
Proof.
  unfold "⊆".
  intros.
  cut (False).
  intros.
  elim H0.
  apply ((proj2_sig exists_empty_set) x).
  assumption.
Qed.

Lemma subset_of_empty_set : ∀ a, a ⊆ ∅ -> a = ∅.
Proof.
  unfold "⊆".
  intros.
  cut (∀ x, x ∈ a <-> x ∈ ∅).
  - intros.
    apply extension.
    assumption.
  - intros.
    split.
    * apply H.
    * apply all_superset_empty_set.
Qed.

Axiom pairing : ∀ a b, { c | a ∈ c ∧ b ∈ c }.

Definition pair_of a b := specification (proj1_sig (pairing a b)) (λ x, x = a ∨ x = b).
Definition pair_of_proj1 a b := proj1_sig (pair_of a b).
Definition pair_of_proj2 a b := proj2_sig (pair_of a b).

Notation "#{ A , B }" := (pair_of_proj1 A B) (at level 0, A at level 99, B at level 99) : set_scope.

Lemma pair_of_equiv : ∀ a b x, x ∈ #{a, b} <-> x = a ∨ x = b.
Proof.
  intros.
  unfold "#{ _ , _ }".
  unfold pair_of.
  split.
  - intros.
    cut (x ∈ (proj1_sig (pairing a b)) ∧ (λ x, x = a ∨ x = b) x).
    * intros.
      elim H0.
      intros.
      assumption.
    * apply specification_belongs.
      assumption.
  - intros.
    elim H.
    * intros.
      rewrite H0.
      cut (a ∈ (proj1_sig (pairing a b))).
      -- intros.
         apply pair_of_proj2.
         split.
         assumption.
         rewrite -> H0 in H.
         assumption.
      -- apply (proj2_sig (pairing a b)).
    * intros.
      rewrite H0.
      cut (b ∈ (proj1_sig (pairing a b))).
      -- intros.
         apply pair_of_proj2.
         split.
         assumption.
         rewrite -> H0 in H.
         assumption.
      -- apply (proj2_sig (pairing a b)).
Qed.

Lemma pair_notation_reflexivity : ∀ a b, #{a, b} = #{b, a}.
Proof.
  intros.
  apply extension.
  split.
  - intros.
    assert (x = a ∨ x = b). {
      apply pair_of_equiv.
      assumption.
    }
    elim H0.
    * intros.
      apply pair_of_equiv.
      right.
      assumption.
    * intros.
      apply pair_of_equiv.
      left.
      assumption.
  - intros.
    assert (x = b ∨ x = a). {
      apply pair_of_equiv.
      assumption.
    }
    elim H0.
    * intros.
      apply pair_of_equiv.
      right.
      assumption.
    * intros.
      apply pair_of_equiv.
      left.
      assumption.
Qed.

Definition singleton_of a := pair_of a a.
Definition singleton_of_proj1 a := proj1_sig (singleton_of a).
Definition singleton_of_proj2 a := proj2_sig (singleton_of a).

Notation "#{ A }" := (singleton_of_proj1 A) (at level 0, A at level 99) : set_scope.

Lemma singleton_of_equiv : ∀ a x, x ∈ #{a} <-> x = a.
Proof.
  intros.
  cut (x ∈ #{a, a} <-> x = a ∨ x = a).
  - intros.
    unfold "#{ _ , _ }" in H.
    unfold "#{ _ }".
    unfold singleton_of.
    split.
    * intros.
      assert (x = a ∨ x = a).
      apply H.
      assumption.
      elim H1.
      all : intros; assumption.
    * intros.
      apply H.
      left.
      assumption.
  - apply pair_of_equiv.
Qed.

Lemma pair_equals_pair : ∀ a b x y, #{x, y} = #{a, b} -> (x = a ∨ x = b) ∧ (y = a ∨ y = b).
Proof.
  intros.
  assert (x ∈ #{x, y}).
  apply pair_of_equiv.
  left.
  reflexivity.

  assert (y ∈ #{x, y}).
  apply pair_of_equiv.
  right.
  reflexivity.

  rewrite H in H0, H1.

  assert (x = a ∨ x = b).
  apply pair_of_equiv.
  assumption.

  assert (y = a ∨ y = b).
  apply pair_of_equiv.
  assumption.

  split.
  all : assumption.
Qed.

Lemma singleton_equals_pair : ∀ a b x, #{x} = #{a, b} <-> x = a ∧ a = b.
Proof.
  intros.
  split.
  - intros.
    assert (a ∈ #{a, b}). {
      apply pair_of_equiv.
      left.
      reflexivity.
    }
    assert (b ∈ #{a, b}). {
      apply pair_of_equiv.
      right.
      reflexivity.
    }
    rewrite <- H in H0, H1.
    assert (a = x). {
      apply singleton_of_equiv.
      assumption.
    }
    assert (b = x). {
      apply singleton_of_equiv.
      assumption.
    }
    split.
    symmetry.
    assumption.
    transitivity x.
    assumption.
    symmetry.
    assumption.
  - intros.
    elim H.
    intros.
    rewrite H0.
    rewrite H1.
    reflexivity.
Qed.

Lemma singleton_equals_singleton : ∀ a x, #{x} = #{a} <-> a = x.
Proof.
  intros.
  split.
  - intros.
    assert (x ∈ #{x}). {
      apply pair_of_equiv.
      left.
      reflexivity.
    }
    rewrite H in H0.
    symmetry.
    apply singleton_of_equiv.
    assumption.
  - intros.
    rewrite H.
    reflexivity.
Qed.

Lemma pair_share_element : ∀ a b c, #{a, b} = #{a, c} <-> b = c.
Proof.
  intros.
  split.
  - intros.
    assert ((a = a ∨ a = c) ∧ (b = a ∨ b = c)). {
      apply pair_equals_pair.
      assumption.      
    }
    elim H0.
    intros.
    elim H1.
    * intros. 
      elim H2.
      + intros.
        rewrite H4 in H.
        assert (#{a} = #{a, a}) by reflexivity. 
        rewrite <- H5 in H.
        assert (a = a ∧ a = c). {
          apply singleton_equals_pair.
          assumption.
        }
        elim H6.
        intros.
        rewrite H4.
        rewrite H8.
        reflexivity.
      + intros.
        assumption.
    * intros.
      elim H2.  
      + intros.
        rewrite <- H3.
        rewrite H4.
        reflexivity.
      + intros.
        assumption.
  - intros.
    rewrite H.
    reflexivity.
Qed.

Axiom union : ∀ a, { b | ∀ x y, x ∈ y ∧ y ∈ a -> x ∈ b }.

Definition union_of a := proj1_sig (specification (proj1_sig (union a)) (λ x, ∃ y, x ∈ y ∧ y ∈ a)).
Definition union_op a b := union_of #{a, b}.

Notation "A ∪ B" := (union_op A B) (at level 50, left associativity) : set_scope.

Lemma union_of_equiv : ∀ x a, x ∈ (union_of a) <-> ∃ b, x ∈ b ∧ b ∈ a.
Proof.
  intros.
  split.
  - intros.
    unfold union_of in H.
    assert (x ∈ (proj1_sig (union a)) ∧ (λ x, ∃ y, x ∈ y ∧ y ∈ a) x).
    apply (specification_belongs (proj1_sig (union a)) (λ x, ∃ y, x ∈ y ∧ y ∈ a)).
    assumption.
    elim H0.
    intros.
    elim H2.
    intros.
    exists x0.
    assumption.
  - intros.
    elim H.
    intros.
    unfold union_of.
    apply specification_belongs.
    split.
    assert (∀ x y, x ∈ y ∧ y ∈ a -> x ∈ (proj1_sig (union a))).
    apply proj2_sig.
    apply (H1 x x0 H0).
    exists x0.
    assumption.
Qed.

Lemma union_op_equiv : ∀ x a b, x ∈ (union_op a b) <-> x ∈ a ∨ x ∈ b.
Proof.
  intros.
  split.
  - intros.
    unfold union_op in H.
    assert (∃ c, x ∈ c ∧ c ∈ #{a, b}).
    apply (proj1 (union_of_equiv x #{a, b})).
    assumption.
    elim H0.
    intros.
    elim H1.
    intros.
    assert (x0 = a ∨ x0 = b).
    apply pair_of_equiv.
    assumption.
    elim H4.
    * intros.
      rewrite H5 in H2.
      left.
      assumption.
    * intros.
      rewrite H5 in H2.
      right.
      assumption.
  - intros.
    unfold union_op.
    unfold union_of.
    apply specification_belongs.
    elim H.
    * intros.
      split.
      + assert (∀ x y, x ∈ y ∧ y ∈ #{a, b} -> x ∈ (proj1_sig (union #{a, b}))).
        apply proj2_sig.
        apply (H1 x a).
        split.
        assumption.
        apply pair_of_equiv.
        left.
        reflexivity.
      + exists a.
        split.
        assumption.
        apply pair_of_equiv.
        left.
        reflexivity.
    * intros.
      split.
      + assert (∀ x y, x ∈ y ∧ y ∈ #{a, b} -> x ∈ (proj1_sig (union #{a, b}))).
        apply proj2_sig.
        apply (H1 x b).
        split.
        assumption.
        apply pair_of_equiv.
        right.
        reflexivity.
      + exists b.
        split.
        assumption.
        apply pair_of_equiv.
        right.
        reflexivity.
Qed.

Lemma union_op_equiv_neg : ∀ x a b, ¬ x ∈ (union_op a b) <-> ¬ x ∈ a ∧ ¬ x ∈ b.
Proof.
  intros.
  assert (¬ x ∈ (union_op a b) <-> ¬ (x ∈ a ∨ x ∈ b)).
  apply not_iff_compat.
  apply union_op_equiv.
  assert (¬ (x ∈ a ∨ x ∈ b) <-> ¬ x ∈ a ∧ ¬ x ∈ b).
  split.
  - intros.
    split.
    * unfold not.
      intros.
      apply H0.
      left.
      assumption.
    * unfold not.
      intros.
      apply H0.
      right.
      assumption.
  - intros.
    elim H0.
    intros.
    unfold not.
    intros.
    elim H3.
    * intros.
      apply H1.
      assumption.
    * intros.
      apply H2.
      assumption.
  - apply (iff_trans H H0).
Qed.

Lemma union_op_empty : ∀ x, union_op x ∅ = x.
Proof.
  intros.
  apply extension.
  intros.
  split.
  - intros.
    assert (x0 ∈ x ∨ x0 ∈ ∅).
    apply (proj1 (union_op_equiv x0 x ∅)).
    assumption.
    elim H0.
    * intros.
      assumption.
    * intros.
      assert (¬ x0 ∈ ∅).
      apply ((proj2_sig (exists_empty_set)) x0).
      assert (False).
      apply H2.
      assumption.
      elim H3.
  - intros.
    apply union_op_equiv.
    left.
    assumption.
Qed.

Lemma union_op_conmutative : ∀ a b, union_op a b = union_op b a.
Proof.
  intros.
  apply extension.
  intros.
  split.
  - intros.
    apply union_op_equiv.
    assert (x ∈ a ∨ x ∈ b).
    apply union_op_equiv.
    assumption.
    elim H0.
    intros.
    right.
    assumption.
    intros.
    left.
    assumption.
  - intros.
    apply union_op_equiv.
    assert (x ∈ b ∨ x ∈ a).
    apply union_op_equiv.
    assumption.
    elim H0.
    intros.
    right.
    assumption.
    intros.
    left.
    assumption.
Qed.

Lemma union_op_assoc : ∀ a b c, union_op a (union_op b c) = union_op (union_op a b) c.
Proof.
  intros.
  apply extension.
  intros.
  split.
  - intros.
    assert (x ∈ a ∨ x ∈ (union_op b c)).
    apply union_op_equiv.
    assumption.
    elim H0.
    * intros.
      assert (x ∈ (union_op a b)).
      apply union_op_equiv.
      left.
      assumption.
      apply union_op_equiv.
      left.
      assumption.
    * intros.
      assert (x ∈ b ∨ x ∈ c).
      apply union_op_equiv.
      assumption.
      elim H2.
      + intros.
        assert (x ∈ (union_op a b)).
        apply union_op_equiv.
        right.
        assumption.
        apply union_op_equiv.
        left.
        assumption.
      + intros.
        apply union_op_equiv.
        right.
        assumption.
  - intros.
    assert (x ∈ (union_op a b) ∨ x ∈ c).
    apply union_op_equiv.
    assumption.
    elim H0.
    * intros.
      assert (x ∈ a ∨ x ∈ b).
      apply union_op_equiv.
      assumption.
      elim H2.
      + intros.
        apply union_op_equiv.
        left.
        assumption.
      + intros.
        assert (x ∈ (union_op b c)).
        apply union_op_equiv.
        left.
        assumption.
        apply union_op_equiv.
        right.
        assumption.
    * intros.
      assert (x ∈ (union_op b c)).
      apply union_op_equiv.
      right.
      assumption.
      apply union_op_equiv.
      right.
      assumption.
Qed.

Lemma union_op_idem : ∀ a, union_op a a = a.
Proof.
  intros.
  apply extension.
  intros.
  split.
  - intros.
    assert (x ∈ a ∨ x ∈ a).
    apply union_op_equiv.
    assumption.
    elim H0.
    all: intros; assumption.
  - intros.
    apply union_op_equiv.
    left.
    assumption.
Qed.

Lemma union_op_subset : ∀ a b, a ⊆ b <-> union_op a b = b.
Proof.
  intros.
  split.
  - intros.
    unfold "⊆" in H.
    apply extension.
    intros.
    split.
    * intros.
      assert (x ∈ a ∨ x ∈ b).
      apply union_op_equiv.
      assumption.
      elim H1.
      + intros.
        apply (H x).
        assumption.
      + intros.
        assumption.
    * intros.
      apply union_op_equiv.
      right.
      assumption.
  - intros.
    unfold "⊆".
    intros.
    assert (x ∈ (union_op a b) <-> x ∈ b).
    apply extension.
    assumption.
    assert (x ∈ (union_op a b)).
    apply union_op_equiv.
    left.
    assumption.
    apply H1.
    assumption.
Qed.

Lemma union_op_singleton : ∀ a b, #{a} ∪ #{b} = #{a, b}.
Proof.
  intros.
  apply extension.
  intros.
  split.
  - intros.
    assert (x ∈ #{a} ∨ x ∈ #{b}).
    apply union_op_equiv.
    assumption.
    elim H0.
    * intros.
      assert (x = a).
      apply singleton_of_equiv.
      assumption.
      apply pair_of_equiv.
      left.
      assumption.
    * intros.
      assert (x = b).
      apply singleton_of_equiv.
      assumption.
      apply pair_of_equiv.
      right.
      assumption.
  - intros.
    assert (x = a ∨ x = b).
    apply pair_of_equiv.
    assumption.
    elim H0.
    * intros.
      apply union_op_equiv.
      left.
      apply singleton_of_equiv.
      assumption.
    * intros.
      apply union_op_equiv.
      right.
      apply singleton_of_equiv.
      assumption.
Qed.

Definition intersection_op a b := proj1_sig (specification a (λ x, x ∈ b)).

Notation "A ∩ B" := (intersection_op A B) (at level 40, left associativity) : set_scope.

Lemma intersection_op_equiv : ∀ a b x, x ∈ (intersection_op a b) <-> x ∈ a ∧ x ∈ b.
Proof.
  intros.
  split.
  - intros.
    assert (x ∈ a ∧ x ∈ b).
    apply (specification_belongs a (λ x, x ∈ b) x).
    assumption.
    assumption.
  - intros.
    apply (specification_belongs a (λ x, x ∈ b) x).
    assumption.
Qed.

Lemma intersection_op_empty : ∀ a, intersection_op a ∅ = ∅.
Proof.
  intros.
  apply extension.
  intros.
  split.
  - intros.
    assert (x ∈ a ∧ x ∈ ∅).
    apply intersection_op_equiv.
    assumption.
    elim H0.
    intros.
    assumption.
  - intros.
    assert False.
    apply ((proj2_sig exists_empty_set) x).
    assumption.
    elim H0.
Qed.

Lemma intersection_op_conm : ∀ a b, intersection_op a b = intersection_op b a.
Proof.
  intros.
  apply extension.
  intros.
  split.
  - intros.
    assert (x ∈ a ∧ x ∈ b).
    apply intersection_op_equiv.
    assumption.
    elim H0.
    intros.
    apply intersection_op_equiv.
    split.
    all: assumption.
  - intros.
    assert (x ∈ b ∧ x ∈ a).
    apply intersection_op_equiv.
    assumption.
    elim H0.
    intros.
    apply intersection_op_equiv.
    split.
    all: assumption.
Qed.

Lemma intersection_op_assoc : ∀ a b c, intersection_op a (intersection_op b c) = intersection_op (intersection_op a b) c.
Proof.
  intros.
  apply extension.
  intros.
  split.
  - intros.
    assert (x ∈ a ∧ x ∈ (intersection_op b c)).
    apply intersection_op_equiv.
    assumption.
    elim H0.
    intros.
    assert (x ∈ b ∧ x ∈ c).
    apply intersection_op_equiv.
    assumption.
    elim H3.
    intros.
    assert (x ∈ (intersection_op a b)).
    apply intersection_op_equiv.
    split.
    assumption.
    assumption.
    apply intersection_op_equiv.
    split.
    assumption.
    assumption.
  - intros.
    assert (x ∈ (intersection_op a b) ∧ x ∈ c).
    apply intersection_op_equiv.
    assumption.
    elim H0.
    intros.
    assert (x ∈ a ∧ x ∈ b).
    apply intersection_op_equiv.
    assumption.
    elim H3.
    intros.
    assert (x ∈ (intersection_op b c)).
    apply intersection_op_equiv.
    split.
    assumption.
    assumption.
    apply intersection_op_equiv.
    split.
    assumption.
    assumption.
Qed.

Lemma intersection_op_idem : ∀ a, intersection_op a a = a.
Proof.
  intros.
  apply extension.
  intros.
  split.
  - intros.
    assert (x ∈ a ∧ x ∈ a).
    apply intersection_op_equiv.
    assumption.
    elim H0.
    intros.
    assumption.
  - intros.
    apply intersection_op_equiv.
    split.
    assumption.
    assumption.
Qed.

Lemma intersection_op_subset : ∀ a b, a ⊆ b <-> intersection_op a b = a.
Proof.
  intros.
  split.
  - intros.
    unfold "⊆" in H.
    apply extension.
    intros.
    split.
    * intros.
      assert (x ∈ a ∧ x ∈ b).
      apply intersection_op_equiv.
      assumption.
      elim H1.
      intros.
      assumption.
    * intros.
      assert (x ∈ b).
      apply H.
      assumption.
      apply intersection_op_equiv.
      split.
      all: assumption.
  - intros.
    unfold "⊆".
    intros.
    assert (x ∈ (intersection_op a b) <-> x ∈ a).
    apply extension.
    assumption.
    assert (x ∈ (intersection_op a b)).
    apply H1.
    assumption.
    assert (x ∈ a ∧ x ∈ b).
    apply intersection_op_equiv.
    assumption.
    elim H3.
    intros.
    assumption.
Qed.

Lemma intersection_op_distributes_over_union_op : ∀ a b c, intersection_op a (union_op b c) = union_op (intersection_op a b) (intersection_op a c).
Proof.
  intros.
  apply extension.
  intros.
  split.
  - intros.
    assert (x ∈ a ∧ x ∈ (b ∪ c)).
    apply intersection_op_equiv.
    assumption.
    elim H0.
    intros.
    assert (x ∈ b ∨ x ∈ c).
    apply union_op_equiv.
    assumption.
    elim H3.
    * intros.
      assert (x ∈ (a ∩ b)).
      apply intersection_op_equiv.
      split.
      assumption.
      assumption.
      apply union_op_equiv.
      left.
      assumption.
    * intros.
      assert (x ∈ (a ∩ c)).
      apply intersection_op_equiv.
      split.
      assumption.
      assumption.
      apply union_op_equiv.
      right.
      assumption.
  - intros.
    assert (x ∈ (a ∩ b) ∨ x ∈ (a ∩ c)).
    apply union_op_equiv.
    assumption.
    elim H0.
    * intros.
      assert (x ∈ a ∧ x ∈ b).
      apply intersection_op_equiv.
      assumption.
      elim H2.
      intros.
      assert (x ∈ (b ∪ c)).
      apply union_op_equiv.
      left.
      assumption.
      apply intersection_op_equiv.
      split.
      all: assumption.
    * intros.
      assert (x ∈ a ∧ x ∈ c).
      apply intersection_op_equiv.
      assumption.
      elim H2.
      intros.
      assert (x ∈ (b ∪ c)).
      apply union_op_equiv.
      right.
      assumption.
      apply intersection_op_equiv.
      split.
      all: assumption.
Qed.

Lemma union_op_distributes_over_intersection_op : ∀ a b c, a ∪ (b ∩ c) = (a ∪ b) ∩ (a ∪ c).
Proof.
  intros.
  apply extension.
  intros.
  split.
  - intros.
    assert (x ∈ a ∨ x ∈ (b ∩ c)).
    apply union_op_equiv.
    assumption.
    elim H0.
    * intros.
      assert (x ∈ (a ∪ b)).
      apply union_op_equiv.
      left.
      assumption.
      assert (x ∈ (a ∪ c)).
      apply union_op_equiv.
      left.
      assumption.
      apply intersection_op_equiv.
      split.
      all: assumption.
    * intros.
      assert (x ∈ b ∧ x ∈ c).
      apply intersection_op_equiv.
      assumption.
      elim H2.
      intros.
      assert (x ∈ (a ∪ b)).
      apply union_op_equiv.
      right.
      assumption.
      assert (x ∈ (a ∪ c)).
      apply union_op_equiv.
      right.
      assumption.
      apply intersection_op_equiv.
      split.
      all: assumption.
  - intros.
    assert (x ∈ (a ∪ b) ∧ x ∈ (a ∪ c)).
    apply intersection_op_equiv.
    assumption.
    elim H0.
    intros.
    assert (x ∈ a ∨ x ∈ b).
    apply union_op_equiv.
    assumption.
    assert (x ∈ a ∨ x ∈ c).
    apply union_op_equiv.
    assumption.
    elim H3.
    * intros.
      apply union_op_equiv.
      left.
      assumption.
    * intros.
      elim H4.
      + intros.
        apply union_op_equiv.
        left.
        assumption.
      + intros.
        assert (x ∈ (b ∩ c)).
        apply intersection_op_equiv.
        split.
        1-2: assumption.
        apply union_op_equiv.
        right.
        assumption.
Qed.

Definition intersection_of a := proj1_sig (specification (union_of a) (λ x, ∀ y, y ∈ a -> x ∈ y)).

Lemma intersection_of_subset : ∀ a x, a ∈ x -> intersection_of x ⊆ a.
Proof.
  intros.
  unfold "⊆".
  intros.
  unfold intersection_of in H0.
  assert (x0 ∈ (union_of x) ∧ (∀ y, y ∈ x -> x0 ∈ y)).
  apply (specification_belongs (union_of x) (λ x0, ∀ y, y ∈ x -> x0 ∈ y) x0).
  assumption.
  elim H1.
  intros.
  apply H3.
  assumption.
Qed.

Lemma union_of_superset : ∀ a x, a ∈ x -> a ⊆ (union_of x).
Proof.
  intros.
  unfold "⊆".
  intros.
  apply union_of_equiv.
  exists a.
  split.
  all: assumption.
Qed.

Definition complement a b := proj1_sig (specification a (λ x, ¬ x ∈ b)).
Notation "A - B" := (complement A B) (at level 50, left associativity).

Lemma complement_equiv : ∀ u a x, x ∈ (u - a) <-> x ∈ u ∧ ¬ x ∈ a.
Proof.
  intros.
  split.
  - intros.
    apply (specification_belongs u (λ x, ¬ x ∈ a) x).
    assumption.
  - intros.
    apply (specification_belongs u (λ x, ¬ x ∈ a) x).
    assumption.
Qed.

Lemma demorgan_union : ∀ u a b, u - (a ∪ b) = (u - a) ∩ (u - b).
Proof.
  intros.
  apply extension.
  split.
  - intros.
    assert (x ∈ u ∧ ¬ x ∈ (a ∪ b)).
    apply complement_equiv.
    assumption.
    elim H0.
    intros.
    assert (¬ x ∈ a ∧ ¬ x ∈ b).
    apply union_op_equiv_neg.
    assumption.
    elim H3.
    intros.
    assert (x ∈ (u - a)).
    apply specification_belongs.
    split.
    1-2: assumption.
    assert (x ∈ (u - b)).
    apply specification_belongs.
    split.
    1-2: assumption.
    apply intersection_op_equiv.
    split.
    all: assumption.
  - intros.
    assert (x ∈ (u - a) ∧ x ∈ (u - b)).
    apply intersection_op_equiv.
    assumption.
    elim H0.
    intros.
    assert (x ∈ u ∧ ¬ x ∈ a).
    apply complement_equiv.
    assumption.
    elim H3.
    intros.
    assert (x ∈ u ∧ ¬ x ∈ b).
    apply complement_equiv.
    assumption.
    elim H6.
    intros.
    assert (¬ x ∈ (a ∪ b)).
    apply union_op_equiv_neg.
    split.
    1-2: assumption.
    apply specification_belongs.
    split.
    all: assumption.
Qed.

Lemma complement_empty : ∀ u, u - ∅ = u ∧ u - u = ∅.
Proof.
  intros.
  split.
  - apply extension.
    intros.
    split.
    * intros.
      assert (x ∈ u ∧ ¬ x ∈ ∅).
      apply complement_equiv.
      assumption.
      exact (proj1 H0).
    * intros.
      apply specification_belongs.
      split.
      + assumption.
      + unfold not.
        intros.
        apply ((proj2_sig (exists_empty_set)) x).
        assumption.
  - apply extension.
    intros.
    split.
    * intros.
      assert (x ∈ u ∧ ¬ x ∈ u).
      apply complement_equiv.
      assumption.
      elim H0.
      intros.
      absurd (x ∈ u).
      assumption.
      assumption.
    * intros.
      assert False.
      apply ((proj2_sig (exists_empty_set)) x).
      assumption.
      elim H0.
Qed.

Lemma complement_intersection : ∀ u a, a ⊆ u -> a ∩ (u - a) = ∅.
Proof.
  intros.
  apply extension.
  intros.
  split.
  - intros.
    assert (x ∈ a ∧ x ∈ (u - a)).
    apply intersection_op_equiv.
    assumption.
    elim H1.
    intros.
    assert (x ∈ u ∧ ¬ x ∈ a).
    apply complement_equiv.
    assumption.
    elim H4.
    intros.
    absurd (x ∈ a).
    assumption.
    assumption.
  - intros.
    assert False.
    apply ((proj2_sig (exists_empty_set)) x).
    assumption.
    elim H1.
Qed.

Axiom power : ∀ a, { b | ∀ x, x ⊆ a -> x ∈ b }.

Definition power_of a := proj1_sig (specification (proj1_sig (power a)) (λ x, x ⊆ a)).

Lemma power_of_equiv : ∀ a x, x ∈ (power_of a) <-> x ⊆ a.
Proof.
  intros.
  split.
  - intros.
    assert (x ∈ (proj1_sig (power a)) ∧ x ⊆ a).
    apply (specification_belongs (proj1_sig (power a)) (λ x, x ⊆ a) x).
    assumption.
    exact (proj2 H0).
  - intros.
    apply (specification_belongs (proj1_sig (power a)) (λ x, x ⊆ a) x).
    split.
    * apply (proj2_sig (power a)).
      assumption.
    * assumption.
Qed.

(* TODO: demorgan_general *)

Lemma subset_of_power : ∀ a b, b ⊆ (power_of a) -> union_of b ⊆ a.
Proof.
  intros.
  unfold "⊆" in H.
  assert (∀ x, x ∈ b -> x ⊆ a). {
    intros.
    apply power_of_equiv.
    apply H.
    assumption.
  }
  unfold "⊆".
  intros.
  assert (∃ c, x ∈ c ∧ c ∈ b). {
    apply union_of_equiv.
    assumption.
  }
  elim H2.
  intros.
  elim H3.
  intros.
  assert (x0 ⊆ a). {
    apply H0.
    assumption.
  }
  unfold "⊆" in H6.
  apply H6.
  assumption.
Qed.

Definition ord_pair_of a b := #{#{a}, #{a, b}}.
Notation "#( A , B )" := (ord_pair_of A B) (at level 0, A at level 99, B at level 99) : set_scope.

Lemma ord_pair_equals_ord_pair : ∀ a b x y, #(a, b) = #(x, y) <-> a = x ∧ b = y.
Proof.
  intros.
  split.
  - intros.
    unfold "#( _ , _ )" in H.
    assert ((#{a} = #{x} ∨ #{a} = #{x, y}) ∧ (#{a, b} = #{x} ∨ #{a, b} = #{x, y})). {
      apply pair_equals_pair.
      assumption.
    }
    elim H0. 
    intros.
    elim H1.
    * intros.
      rewrite H3 in H.
      assert (#{a, b} = #{x, y}). {
        apply (pair_share_element #{x} #{a, b} #{x, y}).
        assumption.
      }
      assert (x = a). {
        apply singleton_equals_singleton.
        assumption.
      }
      rewrite H5 in H4.
      assert (b = y). {
        apply (pair_share_element a b y).
        assumption.
      }
      split.
      + symmetry.
        assumption.
      + assumption.
    * intros.
      assert (a = x ∧ x = y). {
        apply singleton_equals_pair.
        assumption.
      }
      elim H4.
      intros.
      rewrite <- H6 in H.
      assert (#{x} = #{x, x}) by reflexivity.
      rewrite <- H7 in H.
      assert (#{#{x}, #{x}} = #{#{x}}) by reflexivity.
      rewrite H8 in H.
      symmetry in H.
      assert (#{x} = #{a} ∧ #{a} = #{a, b}). {
        apply singleton_equals_pair.
        assumption.
      }
      elim H9.
      intros.
      assert (a = a ∧ a = b). {
        apply singleton_equals_pair.
        assumption.
      }
      elim H12.
      intros.
      split.
      + assumption.
      + rewrite <- H6.
        rewrite <- H14.
        assumption.
  - intros.
    elim H.
    intros.
    rewrite H0, H1.
    reflexivity.
Qed.

Lemma ord_pair_in_power : ∀ a b A B, a ∈ A ∧ b ∈ B -> #(a, b) ∈ (power_of (power_of (A ∪ B))).
Proof.
  intros.
  elim H.
  intros.
  unfold "#( _ , _ )".
  apply power_of_equiv. 
  unfold "⊆".
  intros.
  apply power_of_equiv.
  unfold "⊆".
  intro y.
  intros.
  apply union_op_equiv.
  assert (x = #{a} ∨ x = #{a, b}). {
    apply pair_of_equiv.
    assumption.
  }
  elim H4.
  - intros.
    rewrite H5 in H3.
    assert (y = a). {
      apply singleton_of_equiv.
      assumption.
    }
    rewrite <- H6 in H0.
    left.
    assumption.
  - intros.
    rewrite H5 in H3.
    assert (y = a ∨ y = b). {
      apply pair_of_equiv.
      assumption.
    }
    elim H6.
    * intros.
      rewrite <- H7 in H0.
      left.
      assumption.
    * intros.
      rewrite <- H7 in H1.
      right.
      assumption.
Qed.

Definition cartesian_product a b := proj1_sig (specification (power_of (power_of (a ∪ b))) (λ x, ∃ y z, y ∈ a ∧ z ∈ b ∧ x = #(y, z))).

Notation "A × B" := (cartesian_product A B) (at level 0, right associativity) : set_scope.

Lemma cartesian_product_equiv : ∀ a b A B, a ∈ A ∧ b ∈ B <-> #(a, b) ∈ A × B.
Proof.
  intros.
  split.
  - intros.
    unfold "_ × _".
    apply specification_belongs.
    split.
    * apply ord_pair_in_power.
      assumption.
    * exists a, b.
      split.
      + apply H.
      + split.
        -- apply H.
        -- reflexivity.
  - intros.
    unfold "×" in H.
    assert (#(a, b) ∈ (power_of (power_of (A ∪ B))) ∧ ∃ y z, y ∈ A ∧ z ∈ B ∧ #(a, b) = #(y, z)). {
      apply (specification_belongs (power_of (power_of (A ∪ B))) (λ x, ∃ y z, y ∈ A ∧ z ∈ B ∧ x = #(y, z)) #(a, b)).
      assumption.
    }
    elim H0.
    intros.
    elim H2. 
    intros.
    elim H3.
    intros.
    elim H4.
    intros.
    elim H6.
    intros.
    assert (a = x ∧ b = x0). {
      apply ord_pair_equals_ord_pair.
      assumption.
    }
    elim H9.
    intros.
    rewrite <- H10 in H5.
    rewrite <- H11 in H7.
    split. 
    assumption.
    assumption.
Qed.

Definition relation_from_to r a b := r ⊆ a × b.
Definition relation_in r a := relation_from_to r a a.
Definition domain r a b := specification a (λ x, ∃ y, y ∈ b ∧ #(x, y) ∈ r).
Definition range r a b := specification b (λ y, ∃ x, x ∈ a ∧ #(x, y) ∈ r).

Definition reflexive r a := ∀ x, x ∈ a -> #(x, x) ∈ r.
Definition symetric r a := ∀ x y, x ∈ a ∧ y ∈ a -> (#(x, y) ∈ r -> #(y, x) ∈ r).
Definition transitive r a := ∀ x y z, x ∈ a ∧ y ∈ a ∧ z ∈ a -> (#(x, y) ∈ r ∧ #(y, z) ∈ r -> #(x, z) ∈ r).
Definition antisymetric r a :=
