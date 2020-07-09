Section three_2.
  Variables P Q R T : Prop.
  Lemma id_P : P -> P.
  Proof.
    intro p.
    assumption.
  Qed.

  Lemma id_PP : (P -> P) -> (P -> P).
  Proof.
    intro H6.
    assumption.
  Qed.

  Lemma imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
  Proof.
    intros H H' p.
    apply H'.
    apply H.
    assumption.
  Qed.

  Lemma imp_perm : (P -> Q -> R) -> (Q -> P -> R).
  Proof.
    intros H H' p.
    apply H.
    assumption.
    assumption.
  Qed.

  Lemma ignore_Q : (P -> R) -> P -> Q -> R.
  Proof.
    intros H p q.
    apply H.
    assumption.
  Qed.

  Lemma delta_imp : (P -> P -> Q) -> P -> Q.
  Proof.
    intros H p.
    apply H.
    assumption.
    assumption.
  Qed.

  Lemma delta_impR : (P -> Q) -> (P -> P -> Q).
  Proof.
    intros H p.
    assumption.
  Qed.

  Lemma diamond : (P -> Q) -> (P -> R) -> (Q -> R -> T) -> P -> T.
  Proof.
    intros H H' H'' p.
    apply H''.
    apply H.
    assumption.
    apply H'.
    assumption.
  Qed.

  Lemma weak_peirce : ((((P  -> Q) -> P) -> P) -> Q) -> Q.
  Proof.
    intros H.
    apply H.
    intros H'.
    apply H'.
    intros p.
    apply H.
    intros H''.
    assumption.
  Qed.

End three_2.

  
    
