Require Import Util.
Require Import Lia.

Set Implicit Arguments.

Section Seq.

Variable A : Type.

(* Type definition and basic operations *)

CoInductive Seq :=
  | Nil : Seq
  | Cons : A -> Seq -> Seq.

Definition unfold_seq (s : Seq) := 
  match s with
  | Nil => Nil
  | Cons a tl => Cons a tl
  end.

Definition hd (s : Seq) :=
  match s with
  | Nil => None
  | Cons x _ => Some x
  end.

Definition hd_default (default : A) (s : Seq) :=
  match s with
  | Nil => default
  | Cons x _ => x
  end.

Definition tl (s : Seq) :=
  match s with
  | Nil => None
  | Cons _ ys => Some ys
  end.

Definition tl_default (default : Seq) (s : Seq) :=
  match s with
  | Nil => default
  | Cons _ ys => ys
  end.

Fixpoint nth_tl (n : nat) (s : Seq) :=
  match n with
  | 0 => Some s
  | S m =>
    match tl s with
    | None => None
    | Some ys => nth_tl m ys
    end
  end.

Fixpoint nth_tl_default (default : Seq) (n : nat) (s : Seq) :=
  match n with
  | 0 => s
  | S m =>
    match tl s with
    | None => default
    | Some ys => nth_tl_default default m ys
    end
  end.

Definition nth (n : nat) (s : Seq) :=
  match nth_tl n s with
  | None => None
  | Some ys => hd ys
  end.

(* unfold equality *)

Lemma unfold_seq_eq : forall s, s = unfold_seq s.
Proof.
  intros.
  destruct s.
  - reflexivity.
  - reflexivity.
Qed.

(* Inversion lemmas *)

Lemma hd_inv_nil : forall s : Seq, hd s = None -> s = Nil.
Proof.
  intros.
  destruct s.
  - reflexivity.
  - discriminate H.
Qed.

Lemma hd_inv_cons : forall s a, hd s = Some a -> exists s0, s = Cons a s0.
Proof.
  intros.
  destruct s.
  - discriminate H.
  - injection H.
    intros.
    rewrite H0.
    exists s.
    reflexivity.
Qed.

Lemma tl_inv_nil : forall (s : Seq), tl s = None -> s = Nil.
Proof.
  intros.
  destruct s.
  - reflexivity.
  - discriminate H.
Qed.

Lemma tl_inv_cons : forall (s s0 : Seq), tl s = Some s0 -> exists (a : A), s = Cons a s0.
Proof.
  intros.
  destruct s.
  - discriminate H.
  - injection H.
    intros.
    rewrite H0.
    exists a.
    reflexivity.
Qed.

Lemma nth_tl_inv_none : forall s n, nth_tl (S n) s = None -> s = Nil \/ exists a s', s = Cons a s' /\ nth_tl n s' = None.
Proof.
  intros.
  destruct s.
  - left.
    reflexivity.
  - right.
    exists a.
    exists s.
    split.
    * reflexivity.
    * simpl in H.
      assumption.
Qed.

Lemma nth_inv_none : forall m, nth m Nil = None.
Proof.
  intros.
  destruct m.
  - unfold nth.
    reflexivity.
  - unfold nth.
    reflexivity.
Qed.

Lemma nth_inv_some : forall m s t, nth m s = Some t -> exists a ss, s = Cons a ss.
Proof.
  intros.
  destruct s.
  - pose proof (nth_inv_none m).
    rewrite H0 in H.
    discriminate H.
  - exists a.
    exists s.
    reflexivity.
Qed.

(* Useful lemmas *)

Lemma tl_default_eq_tl : forall s x, tl_default x s = match tl s with Some y => y | None => x end.
Proof.
  intros.
  destruct s.
  - reflexivity.
  - reflexivity.
Qed.

Lemma nth_tl_default_eq_nth_tl : forall n s x, nth_tl_default x n s = match nth_tl n s with Some y => y | None => x end.
Proof.
  intro.
  induction n.
  - intros.
    reflexivity.
  - intros.
    destruct s.
    * reflexivity.
    * simpl.
      apply IHn. 
Qed.

Lemma nth_tl_none_nth_none : forall n s, nth_tl n s = None -> nth n s = None.
Proof.
  intros.
  unfold nth.
  rewrite H.
  reflexivity.
Qed.

Lemma nth_none_nth_tl_none_or_nil : forall n s, nth n s = None -> nth_tl n s = None \/ nth_tl n s = Some Nil.
Proof.
  intros.
  unfold nth in H.
  destruct (nth_tl n s).
  - destruct s0.
    * right.
      reflexivity.
    * discriminate H.
  - left.
    reflexivity.
Qed.

Lemma nth_tl_none_plus_m : forall n m s, nth_tl n s = None -> nth_tl (m + n) s = None.
Proof.
  intros n m.
  destruct m.
  - intros.
    simpl.
    assumption.
  - induction n.
    * intros.
      discriminate H.
    * intros.
      pose proof (nth_tl_inv_none s n H).
      elim H0.
      + intros.
        rewrite H1.
        reflexivity.
      + intros.
        elim H1.
        intros.
        elim H2.
        intros.
        elim H3.
        intros.
        rewrite H4.
        simpl.
        assert (m + S n = S m + n) by lia.
        rewrite H6.
        apply IHn.
        assumption.
Qed.

Lemma tl_nth_tl : forall (n : nat) (s : Seq), x <- nth_tl n s ;; tl x = x <- tl s ;; nth_tl n x.
Proof.
  intro n.
  induction n.
  - intros.
    destruct s.
    * reflexivity.
    * reflexivity.
  - intros.
    destruct s.
    * reflexivity.
    * simpl.
      specialize (IHn s).
      destruct (tl s).
      + simpl in IHn.
        assumption.
      + simpl in IHn.
        assumption.
Qed.

Lemma nth_nth_tl : forall (n m : nat) (s : Seq), x <- nth_tl n s ;; nth m x = nth (m + n) s.
Proof.
  intros.
  apply bind_eq.
  - intros.
    apply nth_tl_none_nth_none.
    apply nth_tl_none_plus_m.
    assumption.
  - intro a.
    generalize s.
    induction n.
    * intros.
      injection H.
      intros.
      rewrite H0.
      assert (m + 0 = m) by lia.
      rewrite H1.
      reflexivity.
    * intros.
      destruct s0.
      + discriminate H.
      + simpl in H.
        pose proof (IHn s0 H).
        assert (m + S n = S (m + n)) by lia.
        rewrite H1.
        unfold nth.
        simpl.
        unfold nth in H0.
        assumption.
Qed.

Lemma nth_of_tl : forall n s, x <- tl s ;; nth n x = nth (1 + n) s.
Proof.
  intros.
  apply bind_eq.
  - intros.
    pose proof (tl_inv_nil s H).
    rewrite H0.
    apply nth_inv_none.
  - intros.
    unfold nth.
    simpl.
    rewrite <- H.
    reflexivity.
Qed.

Lemma nth_none_plus_m : forall n m s, nth n s = None -> nth (m + n) s = None.
Proof.
  intros.
  pose proof (nth_none_nth_tl_none_or_nil n s H).
  elim H0.
  - intros.
    pose proof (nth_tl_none_plus_m n m s H1).
    unfold nth.
    rewrite H2.
    reflexivity.
  - intros.
    pose proof (nth_nth_tl n m s).
    rewrite H1 in H2.
    simpl in H2.
    assert (nth m Nil = None) by apply nth_inv_none.
    rewrite H3 in H2. 
    symmetry in H2.
    pose proof (nth_none_nth_tl_none_or_nil (m + n) s H2).
    elim H4.
    * intros.
      unfold nth.
      rewrite H5.
      reflexivity.
    * intros.
      unfold nth.
      rewrite H5.
      reflexivity.
Qed.

End Seq.

Section Iterate.

Variable A : Type.

CoFixpoint iterate (f : A -> A) (x : A) := Cons x (iterate f (f x)).

Fixpoint n_compose (n : nat) (f : A -> A) : A -> A :=
  match n with
  | 0 => id
  | S m => fun x => f (n_compose m f x)
  end.

Lemma n_compose_f_out : forall n f x, n_compose n f (f x) = f (n_compose n f x).
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

Lemma iterate_nth : forall n x f, nth n (iterate f x) = Some (n_compose n f x).
Proof.
  intro n.
  induction n.
  - intros.
    pattern (iterate f x).
    rewrite unfold_seq_eq.
    simpl. 
    unfold nth.
    unfold id.
    reflexivity.
  - intros.
    pattern (iterate f x).
    rewrite unfold_seq_eq.
    simpl.
    unfold nth.
    simpl.
    pose proof (IHn (f x) f).
    unfold nth in H.
    assert (n_compose n f (f x) = f (n_compose n f x)) by apply n_compose_f_out.
    rewrite H0 in H.
    assumption.
Qed.

End Iterate.

Section Nats.

Definition inc (n : nat) := n + 1.
Definition nats (n : nat) := iterate inc n.

Lemma n_compose_inc : forall n m, n_compose n inc m = m + n.
Proof.
  intros.
  induction m.
  - induction n.
    * reflexivity.
    * simpl.
      rewrite IHn.
      unfold inc.
      lia.
  - induction n.
    * simpl.
      unfold id.
      lia.
    * simpl.
      simpl in IHm.
      unfold inc in IHm at 1.
      assert (m + S n = S (m + n)) by lia.
      rewrite H in IHm.
      assert (n_compose n inc m + 1 = S (n_compose n inc m)) by lia.
      rewrite H0 in IHm.
      injection IHm.
      intros.
      pose proof (IHn H1).
      rewrite H2.
      unfold inc.
      lia.
Qed.

Lemma nth_nats : forall n m, nth m (nats n) = Some (n + m).
Proof.
  intros.
  unfold nats.
  pose proof (iterate_nth m n inc).
  rewrite H.
  apply f_equal.
  apply (n_compose_inc m n).
Qed.

End Nats.

Section Zip.

Variable A B : Type.

CoFixpoint zip (xs : Seq A) (ys : Seq B) : Seq (A * B) :=
  match xs, ys with
  | Cons x xs', Cons y ys' => Cons (x, y) (zip xs' ys')
  | _, _ => Nil (A * B)
  end.

End Zip.
