Set Implicit Arguments.
Declare Scope util_scope.
Open Scope util_scope.

Definition bind [A B : Type] (x : option A) (f : A -> option B) : option B :=
  match x with
  | None => None
  | Some a => f a
  end.

Notation "x >>= f" := (bind x f) (at level 58, left associativity) : util_scope.
Notation "x >> y" := (bind x (fun _ => y)) (at level 58, left associativity) : util_scope.
Notation "x <- y ;; z" := (y >>= (fun x => z)) (at level 61, y at next level, right associativity) : util_scope.
Notation "x ;; z" := (x >> z) (at level 61, right associativity) : util_scope.

Lemma bind_eq : forall [A B : Type] (x : option A) (f : A -> option B) (y : option B), 
  (x = None -> y = None) ->
  (forall a : A, Some a = x -> f a = y) ->
  x >>= f = y.
Proof.
  intros.
  unfold bind.
  destruct x.
  - apply H0.
    reflexivity.
  - symmetry.
    apply H.
    reflexivity.
Qed.
