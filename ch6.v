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

(* 10 *)

Definition next_month : month -> month :=
  month_rec (fun m => month)
            Febuary March April May
            June July August September
            October November December January.

Definition is_jan : month -> Prop :=
  month_rect (fun month => Prop)
             True False False False
             False False False False
             False False False False.

(* 11 *)

Definition bool_to_prop (b : bool) : Prop :=
  match b with
    true => True | _ => False
  end.

Theorem true_not_false : true <> false.
Proof.
  unfold not; intros H.
  change (bool_to_prop false).
  rewrite <- H.
  simpl.
  trivial.
Qed.

(* 12 *)
  
Definition vehicle_to_prop (v : vehicle) : Prop :=
  match v with
    bicycle _ => True
  |  _ => False
  end.

Theorem bi_not_motor : forall n m l: nat,
    bicycle n <> motorized m l.
Proof.
  intros n m l H.
  change (vehicle_to_prop (motorized m l)).
  rewrite <- H.
  simpl.
  trivial.
Qed.

(* 13 *)

Require Import Arith.

Open Scope nat_scope.

Record RatPlus : Set :=
  mkRat {top : nat; bottom:nat; bottom_condition: bottom <> 0}.

Axiom eq_ratplus :
  forall r r',
    top r * bottom r' = top r' * bottom r ->
    r = r'.

Definition r : RatPlus.
  apply (mkRat 2 4); auto with arith.
Defined.

Definition r' : RatPlus.
  apply (mkRat 3 6); auto with arith.
Defined.

Theorem r_r'_eq : r = r'.
Proof.
  apply eq_ratplus; auto.
Qed.

Theorem r_not_r' : r <> r'.
  unfold not. intros H. discriminate H.
Qed.

Theorem rat_contradiction : False.
  absurd (r = r').
  apply r_not_r'.
  apply r_r'_eq.
Qed.

Reset eq_RatPlus.

(* 15 *)

Definition true_under_three (n : nat) : bool :=
  match n with
    0 => true
  | 1 => true
  | 2 => true
  | _ => false
  end.

Eval compute in true_under_three 2.

(* 16 *)

Fixpoint rev_plus (n m : nat) {struct m} : nat :=
  match m with 0 => n | S p => S (rev_plus n p) end.

Eval compute in rev_plus 3 5.

(* 17 *)

Fixpoint sum_f (n : nat) (f : nat -> Z) : Z :=
  match n with
    0 => 0
  | S k => f k + sum_f k f
  end.

(* 18 *)

Fixpoint two_power (n : nat) : nat :=
  match n with
    0 => 1
  | S k => 2 * two_power k
  end.


(* 20 *)

Definition pos_even_bool (p : positive) : bool :=
  match p with xO _ => true | _ => false end.

(* 21 *)

Definition pos_div4 (p : positive) : Z :=
  match p with
    xO (xO n) | xO (xI n) => Zpos n
  | xI (xI n) | xI (xO n) => Zpos n
  | _ => 0
  end.

(* 22 *)

Variable pos_mult : positive -> positive -> positive.

Definition mul (n m : Z) : Z :=
  match n,m with
    Zpos x, Zpos y | Zneg x, Zneg y => Zpos (pos_mult x y)
  | Zpos x, Zneg y | Zneg x, Zpos y => Zneg (pos_mult x y)
  | _,_ => Z0
  end.

(* 23 *)

Inductive l : Set :=
    l_and : l -> l -> l
  | l_or : l -> l -> l
  | not_l : l -> l
  | l_imp : l -> l -> l
  | l_t : l
  | l_f : l.

Fixpoint l_eval (form : l) : l :=
  match form with
  | l_and la lb => match (l_eval la),(l_eval lb) with
                     l_t, l_t => l_t
                   | _,_ => l_f
                   end
  | l_or la lb => match (l_eval la),(l_eval lb) with
                    l_t,_ | _,l_t => l_t
                  | _,_ => l_f
                  end
  | not_l la => match l_eval la with
                  l_t => l_f
                | _ => l_t
                end
  | l_imp la lb => match (l_eval la),(l_eval lb) with
                     _,l_t | l_f, l_f => l_t
                   | _,_ => l_f
                   end
  | l_t => l_t
  | l_f => l_f
  end.

(* 24 *)

Inductive rat : Set :=
  one : rat | n_of_x : rat -> rat | d_of_x : rat -> rat.

(* 25 *)

Inductive Z_btree : Set :=
  Z_leaf : Z_btree | Z_node : Z -> Z_btree -> Z_btree -> Z_btree.

Fixpoint value_present (z : Z) (t : Z_btree) : bool :=
  match t with
    Z_leaf => false
  | Z_node x l r =>
    if Zeq_bool z x then true
    else match value_present z l with
           true => true
         | _ => value_present z r
         end
  end.

(* 26 *)

Fixpoint power (z : Z) (n : nat) : Z :=
  match n with
    0%nat => 1 | S p => z * (power z p)
  end.

Fixpoint discrete_log (p : positive) : nat :=
  match p with
    xH => 0%nat
  | xO n | xI n => S (discrete_log n)
  end.

(* 27 *)


Inductive Z_fbtree : Set :=
  Z_fleaf : Z_fbtree
| Z_fnode : Z -> (bool -> Z_fbtree) -> Z_fbtree.

Fixpoint fzero_present (t : Z_fbtree) : bool :=
  match t with
    Z_fleaf => false
  | Z_fnode z f =>
    if Zeq_bool z 0%Z then true
    else match fzero_present (f true) with
           true => true
         | _ => fzero_present (f false)
         end
  end.

(* 28 *)

Inductive Z_inf_tree : Set :=
  Z_inf_leaf : Z_inf_tree
| Z_inf_branch : Z -> (nat -> Z_inf_tree) -> Z_inf_tree.

Fixpoint sum_or (n : nat) (f : nat -> bool) : bool :=
  match n with
    0 => false
  | S k => if f (S k) then true else sum_or k f
  end.

Fixpoint zero_in_inf (n : nat) (t : Z_inf_tree) : bool :=
  match n,t with
  | S k, Z_inf_branch z f => if Zeq_bool z 0 then true else sum_or k (fun x : nat => zero_in_inf k (f x))
  | Z, Z_inf_branch z _ => Zeq_bool z 0
  | _, Z_inf_leaf => false
  end.

(* 29 *)

Ltac refl := reflexivity.

Theorem plus_n_0 : forall n : nat, n = n + 0.
Proof.
  intro n. elim n. refl.
  intros n' H. simpl. elim H. refl.
Qed.

(* 30 *)

Fixpoint zb_to_zfb  (t : Z_btree) : Z_fbtree :=
  match t with
    Z_leaf => Z_fleaf
  | Z_node x l r =>
      Z_fnode x (fun b : bool => if b
                                 then zb_to_zfb l
                                 else zb_to_zfb r)
  end.

Fixpoint zfb_to_zb  (t : Z_fbtree) : Z_btree :=
  match t with
    Z_fleaf => Z_leaf
  | Z_fnode x f => Z_node x
                          (zfb_to_zb (f true))
                          (zfb_to_zb (f false))
  end.

Theorem zb_to_zfb_and_back :
  forall t : Z_btree, zfb_to_zb (zb_to_zfb t) = t.
Proof.
  induction t.
  simpl; refl.
  simpl; rewrite IHt1; rewrite IHt2; refl.
Qed.

(*
Theorem zfb_to_zb_and_back :
  forall t : Z_fbtree, zb_to_zfb (zfb_to_zb t) = t.
*)

(* 31 *)

Fixpoint mult2 (n : nat) : nat :=
  match n with
    0 => 0
  | S k => S (S (mult2 k))
  end.

Theorem plus_n_eq_x_2 :
  forall n : nat, mult2 n = n + n.
Proof.
  induction n.
  trivial.
  simpl.
  rewrite IHn.
  rewrite plus_n_Sm.
  trivial.
Qed.
  

(* 32 *)

Fixpoint sum_n (n : nat) : nat :=
  match n with
    0 => 0
  | S p => S p + sum_n p
  end.

Theorem sum_n_plus_n : forall n, 2 * sum_n n = n + n.
Proof.
