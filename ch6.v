(* 1 *)

Inductive month : Set :=
    January   | Febuary | March    | April
  | May       | June    | July     | August
  | September | October | November | December.

Inductive season : Set :=
    Winter
  | Spring
  | Summer
  | Autumn.

Definition which_season : month -> season :=
  month_rec (fun month => season)
            Winter Winter Spring
            Spring Spring Summer
            Summer Summer Autumn
            Autumn Autumn Winter.

(* 3 *)

Theorem bool_equal :
  forall b : bool, b = true \/ b = false.
Proof.
  intro b;
    elim b;
    [apply or_introl | apply or_intror];
    apply refl_equal.
Qed.

Reset bool_equal.

Theorem bool_equal :
  forall b : bool, b = true \/ b = false.
Proof.
  intro b; pattern b; apply bool_ind; [left | right]; reflexivity.
Qed.

(* 4 *)

Reset which_season.

Definition which_season (m : month) : season :=
  match m with
     December | January | Febuary => Winter
   | March    | April   | May     => Spring
   | June     | July    | August  => Summer
   | _ => Autumn
  end.

(* 5 *)

Definition even_days (leap : bool) (m : month) : bool :=
  match m with
    April | June | September | November => true
  | Febuary => if leap then false else true
  | _ => false
  end.

(* 6 *)

Definition bool_eq (a b : bool) : bool :=
  match a,b with
    true,true | false,false => true
  | _,_ => false
  end.

Definition bool_not (a : bool) : bool := if a then false else true.

Definition bool_xor (a b : bool) : bool := bool_not (bool_eq a b).

Definition bool_and (a b : bool) : bool :=
  match a,b with
    true,true => true
  | _,_ => false
  end.

Definition bool_or (a b : bool) : bool :=
  match a,b with
    true,_ | _,true => true
  | _,_ => false
  end.

Theorem xor_not_eq : forall b1 b2 : bool,
    bool_xor b1 b2 = bool_not (bool_eq b1 b2).
Proof. trivial. Qed.

Theorem not_and_or_not_not : forall b1 b2 : bool,
    bool_not (bool_and b1 b2) =
    bool_or (bool_not b1) (bool_not b2).
Proof.
  intros b1 b2;
    induction b1; induction b2;
                  simpl; trivial.
Qed.

Theorem not_not_eq_b : forall b : bool,
    bool_not (bool_not b) = b.
Proof.
  intros b; unfold bool_not; induction b; trivial.
Qed.



