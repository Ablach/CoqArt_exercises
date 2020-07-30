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

Theorem not_divides_tl : forall n m : nat, 0 < m -> m < n -> ~ divides n m.
Proof.
  intros n m H H0 H1.
  elim H1; intros x H2.
  rewrite <- H2 in H.
  rewrite <- H2 in H0.
  generalize H H0.
  case x.
  intros H'; absurd (0 < 0 * n); auto with arith.
  intros n0. simpl.
  intros H3 H4.
  absurd (n <= n + n0 * n); auto with arith.
Qed.

Theorem not_lt_2_divides :
  forall n m : nat, n <> 1 -> n < 2 -> 0 < m ->
                    ~ divides n m.
Proof.
  intros n m h h0.
  cut (n = 0).
  intros h1.
  rewrite h1.
  case m.
  intros h2; absurd (0 < 0); [auto with arith | trivial].
  intros n0 h3 h4. elim h4.
  intros n1. omega.
  omega.
Qed.

Theorem  le_plus_minus : forall n m:nat, le n m -> m = n+(m-n).
Proof.  intros n m h.  omega. Qed.

Theorem  lt_lt_or_eq : forall n m:nat, n < S m ->  n<m \/  n=m.
Proof.  intros n m. omega. Qed.
  
                                             
 (*
Zpos_xI  : forall p:positive, Zpos (xI p) = (2 * Zpos p + 1)%Z
Zpos_xO  : forall p:positive, Zpos (xO p) = (2 * Zpos p)%Z
  *)

Ltac repeat_rewrite :=
  match goal with
    |- context [Zpos (xO ?p)] =>
    match p with
      | xH => fail 1
      | ?x2 => rewrite (Zpos_xO x2); repeat_rewrite
    end
  | |- context [Zpos (xI ?p)] =>
    match p with
    | xH => fail 1
    | ?x2 => rewrite (Zpos_xI x2); repeat_rewrite
    end
  | |- _ => idtac
  end.

