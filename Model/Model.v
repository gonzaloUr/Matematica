Require Import Seq.
Declare Scope model_scope.

Module Type TS.
  Parameter State : Set.
  Parameter Action : Set.
  Parameter Atomic : Set.
  Parameter start : State.
  Parameter transition : State -> Action -> option State.
  Parameter label : State -> Atomic -> bool.
End TS.

Module Theory (ts : TS).
  Import ts.

  Inductive StateFormula : Set :=
    | Always : StateFormula
    | Atom : Atomic -> StateFormula
    | And : StateFormula -> StateFormula -> StateFormula
    | Not : StateFormula -> StateFormula
    | One : PathFormula -> StateFormula
    | All : PathFormula -> StateFormula
  with PathFormula : Set :=
    | Next : StateFormula -> PathFormula
    | Globally : StateFormula -> PathFormula
    | Eventually : StateFormula -> PathFormula
    | Until : StateFormula -> StateFormula -> PathFormula.

  Notation "'Exists' x" := (some x) (at level 65, right associativity) : model_scope.
  Notation "'Forall' x" := (every x) (at level 65, right associativity) : model_scope.
  Notation "x /\ y" := (conj x y) (at level 80, right associativity) : model_scope.
  Notation "~ x" := (not x) (at level 75, right associativity) : model_scope.
  Notation "'X x" := (next x) (at level 65, right associativity) : model_scope.
  Notation "'A' x" := (always x) (at level 65, right associativity) : model_scope.
  Notation "'E' x" := (eventually x) (at level 65, right associativity) : model_scope.
  Notation "x 'U' y" := (until x y) (at level 60, right associativity) : model_scope.

  Definition matches (s : State) (ss : Seq State) (accs : Seq Action) :=
    forall (i : nat) (si ssi : State) (ai : Action),
      nth ss i = Some si ->
      nth ss (i + 1) = Some ssi ->
      nth accs i = Some ai ->
      transition si ai = Some ssi.

  Inductive Path := path : forall (s : State) (ss : Seq State) (accs : Seq Action), matches s ss accs -> Path.

  Inductive satisfy : State -> StateFormula -> bool -> Prop :=
    | satisfyT : forall (s : State), satisfy s true true
    | satisfyA0 : forall (s : State) (a : atomic),
        label ts a s = true ->
        satisfy s (atom a) true
    | satisfyA1 : forall (s : State) (a : atomic),
        label ts a s = true ->
        satisfy s (atom a) true
    | satisfyNot : forall (s : State) (f : StateFormula), 
        satisfy s f false -> 
        satisfy s (not f) true
    | satisfyAnd : forall (s : State) (f g : StateFormula),
        satisfy s f true ->
        satisfy s g true ->
        satisfy s (conj f g) true
    | satisfySome : forall (s : State) (p : Path s) (pf : PathFormula),
        satisfyPath s p pf true ->
        satisfy s (some pf) true
    | satisfyEvery : forall (s : State) (pf : PathFormula),
        (forall (p : Path s), satisfyPath s p pf true) ->
        satisfy s (every pf) true
  with satisfyPath : forall s : State, Path s -> PathFormula -> bool -> Prop :=
    | satisfyNext : forall (s0 s1 : State) (p : Path s1) (a : Action) (f : StateFormula),
        transition State Action ts s0 a = Some s1 ->
        satisfy s1 f true ->
        satisfyPath s0 (pathS s0 s1 p a P) (next f) true
    | satisfyAlways : forall (s : State) (p : Path s) (f : StateFormula) (i : nat) (si : State),
      index s p i = Some si -> 
      satisfy si f true -> 
      satisfyPath s p (always f) true
    | satisfyEventually : forall (s : State) (p : Path s) (f : StateFormula),
      (exists (i : nat) (si : State), index s p i = Some si /\ satisfy si f true) ->
      satisfyPath s p (eventually f) true
    | satisfyUntil : forall (s : State) (p : Path s) (f0 f1 : StateFormula), 
      (exists (j : nat) (sj : State), index s p j = Some sj /\ satisfy sj f1 true /\
        (forall (k : nat) (sk : State), 
          k < j ->
          index s p k = Some sk -> 
          satisfy sk f0 true)) ->
      satisfyPath s p (until f0 f1) true.

  Notation "s |= x" := (satisfy s x true) (at level 70, no associativity) : model_scope.
  Notation "s * p |= x" := (satisfyPath s p x true) (at level 70, no associativity) : model_scope.

  Lemma infinitely_often : forall (s : State) (f : StateFormula),
    s |= A F A G f <-> forall p : Path s, exists is : Stream nat, forall (n : nat) (sn : State), index s p (Str_nth n is) = Some sn -> sn |= f.
  Proof.
    split.
    - intros.
      inversion H.
      specialize (H2 p).
      inversion H2.
      elim H6.
      intros.
      elim H7.
      intros.
      elim H8.
      intros.
      inversion H10.
  Abort.
End Theory.
