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


Theorem bool_tex : forall b : bool,
                   (bool_or b (bool_not b)) = true.
Proof.
  intros b; induction b; simpl; trivial.
Qed.

Theorem bool_eq_reflect : forall b1 b2 : bool,
    (bool_eq b1 b2) = true -> b1 = b2.
Proof.
  intros b1 b2; induction b1; induction b2; simpl; trivial.
  intros H; rewrite H; elim H; trivial.
Qed.

Theorem bool_eq_reflect2 : forall b1 b2 : bool,
                           b1 = b2 -> (bool_eq b1 b2) = true.
Proof.
  intros b1 b2. induction b1; induction b2; simpl; trivial.
  intros H; rewrite H; elim H; trivial.
Qed.

Theorem bool_not_or : forall b1 b2 : bool,
    (bool_not (bool_or b1 b2)) =
    (bool_and (bool_not b1) (bool_not b2)).
Proof.
  intros b1 b2; induction b1; induction b2; simpl; trivial.
Qed.

Theorem bool_or_and_distr: forall b1 b2 b3 : bool,
        (bool_or (bool_and b1 b3) (bool_and b2 b3))
        = (bool_and (bool_or b1 b2) b3).
Proof.
  intros b1 b2 b3. induction b1; induction b2; induction b3; simpl; trivial.
Qed.

(* 8 *)

Require Import ZArith.

Open Scope Z_scope.

Record plane : Set := point {abscissa : Z; ordinate : Z}.

Definition manhattan (a b : plane) : Z :=
  (Z.abs (abscissa a - abscissa b)) + (Z.abs (ordinate a - ordinate b)).

(* 9 *)

Inductive vehicle : Set :=
  bicycle : nat -> vehicle | motorized : nat -> nat -> vehicle.

Definition nb_seats : vehicle -> nat :=
  vehicle_rec (fun _ => nat)
              (fun n => n)
              (fun n _ => n).
