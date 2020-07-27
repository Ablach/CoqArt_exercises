Definition divides (n m : nat) := exists p : nat, p*n = m.

Require Import Arith.
Require Import Omega.

Theorem divides_0 : forall n : nat, divides n 0.
Proof.
  intros n. unfold divides. exists 0. auto with arith.
Qed.

Theorem divides_plus : forall n m : nat, divides n m -> divides n (n + m).
Proof.
  intros n m H; elim H; intros p H'; exists (S p). simpl. auto with arith.
Qed.

Theorem not_divides_plus : forall n m : nat, ~divides n m -> ~divides n (n + m).
Proof.
  intros n m H; unfold not; intros H'; elim H'; intros x.
  case x; simpl.
  intros H''; apply H.
  cut (m=0).
  intros H'''; rewrite H'''; apply divides_0.
  omega.
  intros n0 H''; apply H.
  unfold divides; exists n0.
  omega.
Qed.
