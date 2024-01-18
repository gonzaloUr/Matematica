Set Implicit Arguments.
Require Import Util.
Require Import Lia.

Section Seq.

Variable A : Type.

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

Definition tl (s : Seq) :=
  match s with
  | Nil => None
  | Cons _ ys => Some ys
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

Definition nth (n : nat) (s : Seq) :=
  match nth_tl n s with
  | None => None
  | Some ys => hd ys
  end.

CoFixpoint iterate (f : A -> A) (x : A) := Cons x (iterate f (f x)).

Lemma unfold_seq_eq : forall s, s = unfold_seq s.
Proof.
  intros.
  destruct s.
  - reflexivity.
  - reflexivity.
Qed.

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

Lemma nth_tl_none_nth_none : forall n s, nth_tl n s = None -> nth n s = None.
Proof.
  intros.
  unfold nth.
  rewrite H.
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

Fixpoint n_compose (n : nat) (f : A -> A) : A -> A :=
  match n with
  | 0 => id
  | S m => fun x => f (n_compose m f x)
  end.

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
Qed.

End Seq.
