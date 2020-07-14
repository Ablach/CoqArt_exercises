(* 5.1 *)

Lemma id_P : forall P, P -> P.
Proof. intros P H; assumption. Qed.

Lemma id_PP : forall P, (P -> P) -> (P -> P).
Proof. intros P H. assumption. Qed.

Lemma imp_trans : forall P Q R, (P-> Q) -> (Q -> R) -> P -> R.
Proof. intros P Q R H H' p; apply H'; apply H; assumption. Qed.

Lemma imp_perm : forall  P Q R, (P -> Q -> R) -> (Q -> P -> R).
Proof. intros P Q R H H' H''; apply H; assumption. Qed.

Lemma ignore_Q : forall P Q R, (P -> R) -> P -> Q -> R.
Proof. intros P Q R H p q; apply H; assumption. Qed.

Lemma delta_imp : forall P Q, (P -> P -> Q) -> P -> Q.
Proof. intros P Q H p; apply H; assumption. Qed.

Lemma delta_impR : forall P Q, (P -> Q) -> (P -> P -> Q).
Proof. intros P Q H p; assumption. Qed.

Lemma diamond : forall P Q R T, (P -> Q) -> (P -> R) -> (Q -> R -> T) -> P -> T.
Proof.
  intros P Q R T H H' H'' p; apply H''.
  exact (H p).
  exact (H' p).
Qed.

Lemma weak_peirce : forall P Q, ((((P -> Q) -> P) -> P) -> Q) -> Q.
Proof.
  intros P Q H; apply H.
  intros H'; apply H'.
  intros p.

  apply H; intros H''; assumption.
Qed.

(* 5.2 : 4.5 in 4.5 file with tactics *)

(* 5.3 *)

Lemma l1 : ~False.
Proof. intros H; elim H. Qed.

Lemma l2 : forall P : Prop, ~~~P -> ~P.
Proof.
  intros H H' H''. apply H'.
  intros H'''; apply H'''.
  assumption.
Qed.

Lemma l3 : forall P Q : Prop, ~~~P -> P -> Q.
Proof.
  intros P Q nnnp p.
  absurd P.
  apply (l2 P nnnp).
  assumption.
Qed.

Lemma l4 : forall P Q : Prop, (P -> Q) -> ~Q -> ~P.
Proof.
  intros P Q H nq p.
  absurd Q.
  assumption.
  apply H.
  assumption.
Qed.

Lemma l5 : forall P Q R : Prop, (P -> Q) -> (P -> ~Q) -> P -> R.
Proof.
  intros P Q R H H' p.
  absurd Q.
  apply H'; assumption.
  apply H; assumption.
Qed.

(* 5.4 *)

Definition dyslexic_imp := forall P Q : Prop, (P -> Q) -> (Q -> P).

Theorem makeFalse :
  forall P Q : Prop, (P -> Q) -> ~P -> Q -> dyslexic_imp -> False.
Proof.
  intros P Q H np q.
  unfold dyslexic_imp.
  intros H'.
  absurd P.
  assumption.
  eapply H'.
  apply H.
  assumption.
Qed.


(* 5.5 *)

Lemma l6 :
  forall (A : Set) (a b c d : A),
    a=b \/ b=c \/ c=c \/ d=c.
Proof.
  intros A a b c d.
  right; right; left.
  trivial.
Qed.

(* 5.6 *)

Lemma l7 :
  forall A B C : Prop,
    A /\ (B /\ C) -> (A /\ B) /\ C.
Proof.
  intros A B C H.
  split; try apply H.
  split; apply H.
Qed.

Lemma l8 :
  forall A B C D : Prop,
    (A -> B) /\ (C -> D) /\ A /\ C -> B /\ D.
Proof.
  intros A B C D H.
  split; repeat apply H.
Qed.

Lemma l9 :
  forall A : Prop,
    ~(A /\ ~A).
Proof.
  intros A H; absurd A; apply H.
Qed.

Lemma l10 :
  forall A B C : Prop,
    A \/ (B \/ C) -> (A \/ B) \/ C.
Proof.
  intros A B C H.
  elim H.
  intros a; left; left; assumption.
  intros H'.
  elim H'.
  intros b; left; right; assumption.
  intros c; right; assumption.
Qed.


Lemma l11 :
  forall A : Prop,
    ~~(A \/ ~A).
Proof.
  intros A.
  unfold not.
  intros H.
  elim H.
  right.
  intros a.
  apply H.
  left.
  assumption.
Qed.


Lemma l12 :
  forall A B : Prop,
    (A \/ B) /\ ~A -> B.
Proof.
  intros A B H.
  tauto.
Qed.

(* 5.7 *)

Definition peirce := forall P Q : Prop, ((P -> Q) -> P) -> P.
Definition classic := forall P : Prop, ~~P -> P.
Definition lem := forall P : Prop, P \/ ~P.
Definition de_not_and_not := forall P Q : Prop, ~ (~P /\ ~Q) -> P \/ Q.
Definition imp_to_or := forall P Q : Prop, (P -> Q) -> (~P \/ Q).

