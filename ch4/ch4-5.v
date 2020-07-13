Theorem all_perm :
  forall (A : Type) (P : A -> A -> Prop),
    (forall x y : A, P x y) -> forall x y : A, P y x.
Proof. intros A P H x y; apply H. Qed.

Theorem resolution :
  forall (A : Type) (P Q R S : A -> Prop),
    (forall a : A, Q a -> R a -> S a) ->
    (forall b : A, P b -> Q b) ->
    (forall c : A, P c -> R c -> S c).
Proof.
  intros A P Q R S H H' c H0 H1.
  apply H.
  apply H'; assumption.
  assumption.
  Qed.
  
  
