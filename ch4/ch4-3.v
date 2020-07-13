Section chapter4exercise3.
  Variables (A : Set) (P Q : A -> Prop) (R : A -> A -> Prop).

  Theorem all_perm : (forall a b: A, R a b) -> forall a b : A, R b a.
  Proof. intros H a b; apply H. Qed.

  Theorem all_imp_dist :
    (forall a : A , P a -> Q a) -> (forall a : A, P a) -> forall a : A, Q a.
  Proof. intros H H' a; apply H; apply H'. Qed.

  Theorem all_delta : (forall a b : A, R a b) -> forall a : A, R a a.
  Proof. intros H a; apply H. Qed.  
  
End chapter4exercise3.
    
