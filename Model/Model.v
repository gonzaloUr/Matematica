Require Import Coq.Strings.String.
Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.List.

Section Formule.

Inductive term : Set :=
  | variable : string -> term
  | constant : string -> term
  | functor : string -> list term -> term.

Fixpoint FV (t : term) : set string :=
  match t with
  | variable s => cons s (empty_set string)
  | constant _ => empty_set string
  | functor _ fs => fold_left (set_union string_dec) (map FV fs) (empty_set string)
  end.

Definition atomic := {x : term | FV x = empty_set string}.

Inductive StateFormula : Set :=
  | t : StateFormula
  | atom : atomic -> StateFormula
  | conj : StateFormula -> StateFormula -> StateFormula
  | not : StateFormula -> StateFormula
  | some : PathFormula -> StateFormula
  | every : PathFormula -> StateFormula
with PathFormula : Set :=
  | next : StateFormula -> PathFormula
  | until : StateFormula -> StateFormula -> PathFormula.

End Formule.

Section TS.

Variable A B : Set.
Variable A_eq_dec : forall x y : A, {x = y} + {x <> y}.
Variable B_eq_dec : forall x y : B, {x = y} + {x <> y}.

Record TS := {
  states : set A ;
  actions : set B ;
  transition : A -> B -> option A ;
  initial : set A ;
  label : atomic -> A -> option bool
}.

CoInductive Path (ts : TS) : A -> A -> Prop :=
  | path0 : forall s : A, Path ts s s
  | pathS : forall (s0 s1 e : A) (p : Path ts s1 e) (a : B), transition ts s0 a = Some s1 -> Path ts s0 e.

Inductive FinitePath (ts : TS) : forall (s e : A) (p : Path ts s e), Prop :=
  | finite_path_0 : forall s : A, FinitePath ts s s (path0 ts s)
  | finite_path_S : forall (s0 s1 e : A) (p : Path ts s1 e) (a : B) (p_trans : transition ts s0 a = Some s1), FinitePath ts s1 e p -> FinitePath ts s0 e (pathS ts s0 s1 e p a p_trans).

Lemma path_trans : forall (ts : TS) (s se e : A) (p0 : Path ts s se) (p1 : Path ts se e), FinitePath ts s se p0 -> {p2 : Path ts s e | FinitePath ts s e p2}.
Proof.
  intros.
  inversion H.
  - exists p
Qed.

Inductive satisfy : TS -> A -> StateFormula -> Prop :=
  | satisfyT : forall (ts : TS) (s : A), satisfy ts s t
  | satisfyA : forall (ts : TS) (s : A) (a : atomic), label ts a s = Some true -> satisfy ts s (atom a)
  | satisfyNot : forall (ts : TS) (s : A) (f : StateFormula), satisfy ts s f -> satisfy ts s (not f)
  | satisfyAnd : forall (ts : TS) (s : A) (f g : StateFormula), satisfy ts s f -> satisfy ts s g -> satisfy ts s (conj f g)
  | satisfySome : forall (ts : TS) (s e : A) (p : Path ts s e) (pf : PathFormula), satisfyPath ts s e p pf -> satisfy ts s (some pf)
  | satisfyEvery : forall (ts : TS) (s : A) (pf : PathFormula), (forall (e : A) (p : Path ts s e), satisfyPath ts s e p pf) -> satisfy ts s (every pf)
with satisfyPath : forall (ts : TS) (s e : A), Path ts s e -> PathFormula -> Prop :=
  | satisfyNext : forall (ts : TS) (s0 s1 e : A) (p : Path ts s1 e) (a : B) (p_trans : transition ts s0 a = Some s1) (f : StateFormula), 
    satisfy ts s1 f -> satisfyPath ts s0 e (pathS ts s0 s1 e p a p_trans) (next f).
  | satisfyUntil : forall (ts : TS) (s e : A) (p : Path ts s e) (f0 f1 : StateFormula), 

End TS.