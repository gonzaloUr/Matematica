Set Implicit Arguments.
Require Import Lia.
Require Import Seq.
Require Import Util.
Declare Scope model_scope.
Open Scope model_scope.

Parameter State : Set.
Parameter Action : Set.
Parameter Atomic : Set.
Parameter start : State.
Parameter transition : State -> Action -> option State.
Parameter label : State -> Atomic -> bool.

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

Definition matches (ss : Seq State) (accs : Seq Action) := forall i,
  si <- nth i ss ;; ai <- nth i accs ;; transition si ai = nth (i + 1) ss.

Lemma matches_nth_tl : forall n ss ss_n accs accs_n,
  matches ss accs -> nth_tl n ss = Some ss_n -> nth_tl n accs = Some accs_n -> matches ss_n accs_n.
Proof.
  intros.
  unfold matches.
  unfold matches in H.
  intros.
  - apply bind_eq.
    * intros.
      assert (i + 1 = 1 + i) by lia.
      rewrite H3.
      apply (nth_none_plus_m i 1 ss_n).
      assumption.
    * intros.
      apply bind_eq.
      + intros.
        specialize (H (i + n)).
        pose proof (nth_nth_tl n (i + 1) ss).
        rewrite H0 in H4.
        simpl in H4.
        rewrite H4.

        pose proof (nth_nth_tl n i accs).
        rewrite H1 in H5.
        simpl in H5.
        rewrite H3 in H5.
        rewrite <- H5 in H.

        pose proof (nth_nth_tl n i ss).
        rewrite H0 in H6.
        simpl in H6.
        rewrite <- H2 in H6.
        rewrite <- H6 in H.

        simpl in H. 
        symmetry in H.
        assert (i + 1 + n = i + n + 1 ) by lia.
        rewrite H7.
        assumption.
      + intros.
        specialize (H (i + n)).

        pose proof (nth_nth_tl n i accs).
        rewrite H1 in H4.
        simpl in H4.
        rewrite <- H3 in H4.
        rewrite <- H4 in H.

        pose proof (nth_nth_tl n i ss).
        rewrite H0 in H5.
        simpl in H5.
        rewrite <- H2 in H5.
        rewrite <- H5 in H.

        simpl in H.
        rewrite H.
        pose proof (nth_nth_tl n (i + 1) ss).
        rewrite H0 in H6.
        simpl in H6.
        symmetry.
        assert (i + n + 1 = i + 1 + n) by lia.
        rewrite H7.
        assumption.
Qed.

Lemma matches_tl : forall (ss ss_tl : Seq State) (accs accs_tl : Seq Action),
  matches ss accs -> tl ss = Some ss_tl -> tl accs = Some accs_tl -> matches ss_tl accs_tl.
Proof.
  intros.
  apply (matches_nth_tl 1 H).
  - unfold nth_tl.
    rewrite H0.
    reflexivity.
  - unfold nth_tl.
    rewrite H1.
    reflexivity.
Qed.

Inductive Path := path : forall (ss : Seq State) (accs : Seq Action), matches ss accs -> Path.

Definition hd_Path (p : Path) :=
  let (ss, _, _) := p in hd ss.

Section OptionEq.

Variable A : Type.

Definition option_with_eq (x : option A) : option {y : A | x = Some y} := 
  match x as o return option {y : A | o = Some y} with
  | Some a => Some (exist (fun y : A => Some a = Some y) a eq_refl)
  | None => None
  end.

Lemma option_with_eq_nil : forall x, option_with_eq x = None -> x = None.
Proof.
  intros.
  destruct x.
  - discriminate H.
  - reflexivity.
Qed.

End OptionEq.

Definition tl_Path (p : Path) : option Path :=
  let (ss, accs, P) := p in
  match option_with_eq (tl ss), option_with_eq (tl accs) with
  | Some (exist _ ss_tl P_ss_tl), Some (exist _ accs_tl P_accs_tl) =>
    Some (path (matches_tl P P_ss_tl P_accs_tl))
  | _, _ => None
  end.

Definition nth_tl_Path (n : nat) (p : Path) : option Path :=
  let (ss, accs, P) := p in
  match option_with_eq (nth_tl n ss), option_with_eq (nth_tl n accs) with
  | Some (exist _ ss_n P_ss_n), Some (exist _ accs_n P_accs_n) => 
    Some (path (matches_nth_tl n P P_ss_n P_accs_n))
  | _, _ => None
  end.

Definition nth_Path (n : nat) (p : Path) :=
  match nth_tl_Path n p with
  | Some p' => hd_Path p'
  | None => None
  end.

Lemma nth_tl_Path_none : forall ss accs P n,
  nth_tl_Path n (@path ss accs P) = None -> nth_tl n ss = None \/ nth_tl n accs = None.
Proof.
  intros.
  unfold nth_tl_Path in H.
  pose proof (@option_with_eq_nil (Seq State) (nth_tl n ss)).
  pose proof (@option_with_eq_nil (Seq Action) (nth_tl n accs)).
  destruct (option_with_eq (nth_tl n ss)).
  - destruct (option_with_eq (nth_tl n accs)).
    * destruct s.
      destruct s0.
      discriminate H.
    * right.
      apply H1.
      reflexivity.
  - left.
    apply H0.
    reflexivity.
Qed.

Lemma nth_nth_tl_path : forall p n i, x <- nth_tl_Path n p ;; nth_Path i x = nth_Path (n + i) p.
Proof.
  intros.
  apply bind_eq.
  - intros.
    destruct p.
    pose proof (@nth_tl_Path_none ss accs m n H).
    unfold nth_Path.
    unfold nth_tl_Path.
    elim H0.
    * intros.
      pose proof (nth_tl_none_plus_m n i ss H1).
      assert (i + n = n + i) by lia.
      rewrite  H3 in H2.
      rewrite H2.
Abort.

Inductive satisfy : State -> StateFormula -> bool -> Prop :=
  | satisfyAlways : forall s : State, satisfy s Always true
  | satisfyAtom : forall (s : State) (a : Atomic), satisfy s (Atom a) (label s a)
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
      (forall (n : nat) (sn : State), nth_Path n p = Some sn -> satisfy sn f1 false \/ (exists (k : nat) (sk : State), k < n -> nth_Path k p = Some sk -> satisfy sk f0 false)) ->
      satisfyPath p (Until f0 f1) false.

Notation "s |= x" := (satisfy s x true) (at level 70, no associativity) : model_scope.
Notation "s * p |= x" := (satisfyPath s p x true) (at level 70, no associativity) : model_scope.

Lemma many_often : forall (s : State) (f : StateFormula), s |= Forall E Forall G f <-> 
  forall p : Path, hd_Path p = Some s -> exists is : Seq nat, forall (n i : nat) (si : State), nth n is = Some i -> nth_Path i p = Some si -> si |= f.
Proof.
  intros.
  split.
  - intros.
    inversion H.
    specialize (H3 p H0).
    inversion H3.
    inversion H7.
    assert (exists pn : Path, nth_tl_Path n p = Some pn). {
      unfold nth_Path in H5.
      destruct (nth_tl_Path n p).
      - exists p1.
        reflexivity.
      - discriminate H5.
    }
    elim H11.
    intros.
    unfold nth_Path in H5.
    rewrite H12 in H5.
    specialize (H10 x H5).
    inversion H10.
    exists (nats n).
    intros.
    pose proof (nth_nats n n0).
    rewrite H16 in H18.
    injection H18.
    intros.
    rewrite H19 in H17.
Abort.
