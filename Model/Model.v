Require Import Lia.
Require Import Seq.
Require Import Util.

Set Implicit Arguments.
Declare Scope model_scope.
Open Scope model_scope.

Parameter State : Set.
Parameter Action : Set.
Parameter transition : State -> Action -> State -> Prop.
Parameter Atomic : Set.
Parameter start : State.
Parameter label : State -> Atomic -> Prop.

Inductive StateFormula : Set :=
  | Always : StateFormula
  | Atom : Atomic -> StateFormula
  | Not : StateFormula -> StateFormula
  | And : StateFormula -> StateFormula -> StateFormula
  | Exists : PathFormula -> StateFormula
  | Forall : PathFormula -> StateFormula
with PathFormula : Set :=
  | Next : StateFormula -> PathFormula
  | Globally : StateFormula -> PathFormula
  | Eventually : StateFormula -> PathFormula
  | Until : StateFormula -> StateFormula -> PathFormula.

Notation "! x" := (not x) (at level 75, right associativity) : model_scope.
Notation "x & y" := (conj x y) (at level 80, right associativity) : model_scope.
Notation "'Exists' x" := (Exists x) (at level 65, right associativity) : model_scope.
Notation "'Forall' x" := (Forall x) (at level 65, right associativity) : model_scope.

Notation "'X' x" := (Next x) (at level 65, right associativity) : model_scope.
Notation "'G' x" := (Globally x) (at level 65, right associativity) : model_scope.
Notation "'E' x" := (Eventually x) (at level 65, right associativity) : model_scope.
Notation "x 'U' y" := (Until x y) (at level 60, right associativity) : model_scope.

Definition matches (ss : Seq State) (accs : Seq Action) := forall i si ai ssi,
  nth i ss = Some si ->
  nth i accs = Some ai ->
  nth (i + 1) ss = Some ssi ->
  transition si ai ssi.

Lemma matches_nil : matches (Nil State) (Nil Action).
Proof.
  unfold matches.
  intros.
  pose proof (nth_inv_none State i).
  rewrite H2 in H.
  discriminate H.
Qed.

Lemma matches_tl_default : forall ss accs,
  matches ss accs -> matches (tl_default (Nil State) ss) (tl_default (Nil Action) accs).
Proof.
  intros.
  unfold matches.
  unfold matches in H.
  intros.
  apply (H (1 + i)).
  - pose proof (nth_of_tl i ss).
    pose proof (tl_default_eq_tl ss (Nil State)).
    destruct ss.
    * rewrite H4 in H0.
      simpl in H0.
      pose proof (nth_inv_none State i).
      rewrite H5 in H0.
      discriminate H0.
    * rewrite H4 in H0.
      simpl in H0.
      unfold nth.
      simpl.
      unfold nth in H0.
      assumption.
  - pose proof (nth_of_tl i accs).
    pose proof (tl_default_eq_tl accs (Nil Action)).
    destruct accs.
    * rewrite H4 in H1.
      simpl in H1.
      pose proof (nth_inv_none Action i).
      rewrite H5 in H1.
      discriminate H1.
    * rewrite H4 in H1.
      simpl in H1.
      unfold nth.
      simpl.
      unfold nth in H1.
      assumption.
  - pose proof (nth_of_tl (i + 1) ss).
    pose proof (tl_default_eq_tl ss (Nil State)).
    destruct ss.
    * rewrite H4 in H2.
      simpl in H2.
      pose proof (nth_inv_none State (i + 1)).
      rewrite H5 in H2.
      discriminate H2.
    * rewrite H4 in H2.
      simpl in H2.
      unfold nth.
      simpl.
      unfold nth in H0.
      assumption.
Qed.

Lemma matches_nth_tl_default : forall n ss accs, 
  matches ss accs -> matches (nth_tl_default (Nil State) n ss) (nth_tl_default (Nil Action) n accs).
Proof.
  intros.
  unfold matches.
  unfold matches in H.
  intros.
  apply (H (i + n)).
  - pose proof (nth_tl_default_eq_nth_tl n ss (Nil State)).
    rewrite H3 in H0.
    pose proof (nth_nth_tl n i ss).
    rewrite <- H4.
    unfold "_ <- _ ;; _".
    destruct (nth_tl n ss).
    * assumption.
    * pose proof (nth_inv_none State i).
      rewrite H5 in H0.
      discriminate H0.
  - pose proof (nth_tl_default_eq_nth_tl n accs (Nil Action)).
    rewrite H3 in H1.
    pose proof (nth_nth_tl n i accs). 
    rewrite <- H4.
    unfold " _ <- _ ;; _".
    destruct (nth_tl n accs).
    * assumption.
    * pose proof (nth_inv_none Action i).
      rewrite H5 in H1.
      discriminate H1.
  - pose proof (nth_tl_default_eq_nth_tl n ss (Nil State)).
    rewrite H3 in H2.
    pose proof (nth_nth_tl n (i + 1) ss).
    assert (i + 1 + n = i + n + 1) by lia.
    rewrite H5 in H4.
    rewrite <- H4.
    unfold "_ <- _ ;; _".
    destruct (nth_tl n ss).
    * assumption.
    * pose proof (nth_inv_none State (i + 1)).
      rewrite H6 in H2.
      discriminate H2.
Qed.

Definition Path : Type := (Seq State) * (Seq Action).

Definition correct (p : Path) := matches (fst p) (snd p).

Definition hd_Path (p : Path) := hd (fst p).

Definition tl_Path (p : Path) := (tl_default (Nil State) (fst p), tl_default (Nil Action) (snd p)).

Definition nth_tl_Path (n : nat) (p : Path) := (nth_tl_default (Nil State) n (fst p), nth_tl_default (Nil Action) n (snd p)).

Definition nth_Path (n : nat) (p : Path) := nth n (fst p).

Lemma correct_tl : forall p, correct p -> correct (tl_Path p).
Proof.
  intros.  
  unfold correct.
  unfold matches.
  intros.
  unfold correct in H.
  unfold matches in H.
  unfold tl_Path in H0, H1, H2.
  simpl in H0, H1, H2.
  apply (H (1 + i)).
Abort.

Inductive satisfy : State -> StateFormula -> bool -> Prop :=
  | satisfyAlways : forall s : State, satisfy s Always true
  | satisfyAtomTrue : forall (s : State) (a : Atomic), label s a -> satisfy s (Atom a) true
  | satisfyAtomFalse : forall (s : State) (a : Atomic), ~ label s a -> satisfy s (Atom a) false
  | satisfyNot : forall (s : State) (f : StateFormula) (b : bool), 
      satisfy s f b ->
      satisfy s (Not f) (negb b)
  | satisfyAnd : forall (s : State) (f0 f1 : StateFormula) (b0 b1 : bool),
      satisfy s f0 b0 ->
      satisfy s f1 b1 ->
      satisfy s (And f0 f1) (b0 && b1)
  | satisfyExistsTrue : forall (s : State) (pf : PathFormula) (p : Path),
      hd_Path p = Some s ->
      satisfyPath p pf true ->
      satisfy s (Exists pf) true
  | satisfyExistsFalse : forall (s : State) (pf : PathFormula),
      (forall (p : Path), hd_Path p = Some s -> satisfyPath p pf false) ->
      satisfy s (Exists pf) false
  | satisfyForallTrue : forall (s : State) (pf : PathFormula),
      (forall (p : Path), hd_Path p = Some s -> satisfyPath p pf true) ->
      satisfy s (Forall pf) true
  | satisfyForallFalse : forall (s : State) (pf : PathFormula) (p : Path),
      hd_Path p = Some s ->
      satisfyPath p pf false ->
      satisfy s (Forall pf) false
with satisfyPath : Path -> PathFormula -> bool -> Prop :=
  | satisfyNext : forall (p : Path) (f : StateFormula) (sn : State) (b : bool),
      nth_Path 1 p = Some sn ->
      satisfy sn f b ->
      satisfyPath p (Next f) (negb b)
  | satisfyGloballyTrue : forall (p : Path) (f : StateFormula),
      (forall (n : nat) (sn : State), nth_Path n p = Some sn -> satisfy sn f true) ->
      satisfyPath p (Globally f) true
  | satisfyGloballyFalse : forall (p : Path) (f : StateFormula) (n : nat) (sn : State),
      nth_Path n p = Some sn -> 
      satisfy sn f false ->
      satisfyPath p (Globally f) false
  | satisfyEventuallyTrue : forall (p : Path) (f : StateFormula) (n : nat) (sn : State),
      nth_Path n p = Some sn ->
      satisfy sn f true ->
      satisfyPath p (Eventually f) true
  | satisfyEventuallyFalse : forall (p : Path) (f : StateFormula),
      (forall (n : nat) (sn : State), nth_Path n p = Some sn -> satisfy sn f false) ->
      satisfyPath p (Eventually f) false
  | satisfyUntilTrue : forall (p : Path) (f0 f1 : StateFormula) (n : nat) (sn : State),
      nth_Path n p = Some sn -> 
      satisfy sn f1 true ->
      (forall (k : nat) (sk : State), k < n -> nth_Path k p = Some sk -> satisfy sk f0 true) ->
      satisfyPath p (Until f0 f1) true
  | satisfyUntilFalse : forall (p : Path) (f0 f1 : StateFormula),
      (forall (n : nat) (sn : State), 
        nth_Path n p = Some sn -> 
        satisfy sn f1 false \/ (exists (k : nat) (sk : State), k < n -> nth_Path k p = Some sk -> satisfy sk f0 false)) ->
      satisfyPath p (Until f0 f1) false.

Notation "s |= x" := (satisfy s x true) (at level 70, no associativity) : model_scope.
Notation "s * p |= x" := (satisfyPath s p x true) (at level 70, no associativity) : model_scope.

Lemma many_often : forall (s : State) (f : StateFormula), s |= Forall E Forall G f <-> 
  forall p : Path, hd_Path p = Some s -> exists is : Seq nat, forall (n i : nat) (si : State), nth n is = Some i -> nth_Path i p = Some si -> si |= f.
Proof.
  intros.
  split.
  - intros.
    inversion_clear H.
    specialize (H1 p H0).
    inversion_clear H1.
    inversion_clear H2.
    assert (exists pn : Path, nth_tl_Path n p = pn). {
      unfold nth_Path in H.
      destruct (nth_tl_Path n p).
      exists (path m).
      reflexivity.
    }
    elim H2.
    intros.
    unfold nth_Path in H.
    rewrite H3 in H.
    specialize (H1 x H).
    inversion_clear H1.
    exists (nats n).
    intros.
    pose proof (nth_nats n n0).
    rewrite H6 in H1.
    injection H1.
    intros.
    rewrite <- H7 in H5.

    rewrite H16 in H18.
    injection H18.
    intros.
    rewrite H19 in H17.
Abort.
