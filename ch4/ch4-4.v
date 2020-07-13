Section chapter4exercise4.

  Definition id (A : Set) (a : A) : A := a.

  Definition diag (A B : Set) (f : A -> A -> B) (a : A) : B :=
    f a a.

  Definition permute (A B C : Set) (f : A -> B -> C) (b : B) (a : A) : C :=
    f a b.

  Require Import ZArith.
  
  Definition f_nat_Z (A : Set) (f : nat -> A) (z : Z) : A :=
    f (Z.to_nat z).

End chapter4exercise4.
