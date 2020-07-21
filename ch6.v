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
  one : rat | N : rat -> rat | D : rat -> rat.

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

(* misprint?  *)
  
(* 33 *)

Require Import Arith.

Theorem n_lt_sum_n :
  forall n : nat, n <= sum_n n.
Proof.
  induction n.
  refl.
  simpl.
  rewrite le_n_S.
  2: apply IHn.
  rewrite plus_n_Sm.
  apply le_plus_r.
Qed.

(* 34 *)

Require Import List.

Definition fst_2 (A : Set) (l : list A) : list A :=
  match l with
    x :: y :: _ => x :: y :: nil
  | _ => nil
  end.

(* 35 *)
  
Fixpoint fst_n (A : Set) (n : nat) (l : list A) {struct n} : list A :=
  match n,l with
    S k, x :: xs => x :: fst_n _ k xs
  | _,_ => nil
  end.

(* 36 *)

Fixpoint sum_list (l : list Z) : Z :=
  match l with
    x :: xs => x + sum_list xs
  | _ => 0
  end.

(* 37 *)

Fixpoint n_ones (n : nat) : list Z :=
  match n with  
    S k => 1%Z :: n_ones k
  | O => nil
  end.

(* 38 *)

Fixpoint one_to_n (n : nat) : list Z :=
  match n with
    O => nil
  | S k => one_to_n k ++ Z.of_nat (S k) :: nil
  end.

(* 39 *)

Fixpoint nth_option (A:Set)(n:nat)(l:list A) {struct l}
  : option A :=
  match n, l with
  | O, cons a tl =>  Some a
  | S p, cons a tl => nth_option _ p tl
  | n, nil => None
  end.

Fixpoint nth_option' (A : Set) (n : nat) (l : list A) {struct n}
  : option A :=
  match n,l with
    O, a :: t => Some a
  | S k, a :: t => nth_option _ k t
  | n, nil => None
  end.

Theorem nth_eq_prime :
  forall (A : Set) (n : nat) (l : list A),
    nth_option A n l = nth_option' A n l.
Proof.
  intros A n l. induction n; induction l; simpl; trivial.
Qed.

(* 40 *)

Theorem none_means_shorter :
  forall (A : Set) (n : nat) (l : list A),
    nth_option A n l = None -> length l <= n.
Proof.
  simple induction n.
  destruct l0. simpl. trivial.
  simpl. intros H. absurd (Some a = None). discriminate H.
  assumption.
  intros n0 H l H'.
  destruct l. simpl. auto with arith.
  simpl. auto with arith.
Qed.

(* 41 *)

Fixpoint la_to_fa (A : Set) (f : A -> bool) (l : list A) {struct l} : option A :=
  match l with
    x :: xs => if f x then Some x else la_to_fa _ f xs
  | _ => None
  end.

(* 42 *)

Fixpoint split_pairs (A B : Set) (l : list (A*B)) {struct l} : (list A) * (list B) :=
  match l with
    (a,b) :: ps => ((a :: fst (split_pairs _ _ ps)) , (b :: snd (split_pairs _ _ ps)))
  | _ => (nil,nil)
  end.

Fixpoint combine (A B : Set) (la : list A) (lb : list B) {struct la} : list (A*B) :=
  match la,lb with
    x::xs,y::ys => (x,y) :: combine _ _ xs ys
  | _,_ => nil
  end.

Theorem cmb_split_eq_og :
  forall (A B : Set) (l : list (A*B)), combine A B (fst (split_pairs A B l)) (snd (split_pairs A B l)) = l.
Proof.
  induction l0. simpl. trivial.
  case a. intros a0 b. simpl. rewrite IHl0. trivial.
Qed.

(* 43 *)

Inductive btree (A : Set) : Set :=
  leaf : btree A
| node : A -> btree A -> btree A -> btree A.

Fixpoint Z_to_btree (t : Z_btree) : btree Z :=
  match t with
    Z_leaf => leaf _
  | Z_node x l r => node _ x (Z_to_btree l) (Z_to_btree r)
  end.

Fixpoint btree_to_ztree (t : btree Z) : Z_btree :=
  match t with
    leaf _ => Z_leaf
  | node _ x l r => Z_node x (btree_to_ztree l) (btree_to_ztree r)
  end.

Theorem iso_btree_z_zbtree :
  forall t : Z_btree, btree_to_ztree (Z_to_btree t) = t.
Proof.
  intros t. induction t.
  simpl; trivial.

  simpl; rewrite IHt1; rewrite IHt2; trivial.
Qed.

(* 44 *)

(*
Inductive rat : Set :=
  one : rat | N : rat -> rat | D : rat -> rat.
 *)

Fixpoint frac (r : rat) : nat * nat :=
  match r with
    one => (1,1)
  | N r => let (n,d) := frac r in (n + d, d)
  | D r => let (n,d) := frac r in (d, n + d)
  end.


(* 45 / 46 skipping till later *)

Inductive htree (A : Set) : nat -> Set :=
  hleaf : A -> htree A 0
| hnode : forall n : nat, A -> htree A n -> htree A n -> htree A (S n).

(* 47 *)

Fixpoint n_to_tree (n : nat) : htree Z n :=
  match n with
    S k => hnode _ _ (Z.of_nat (S k)) (n_to_tree k) (n_to_tree k)
  | O => hleaf Z 0%Z
  end.

(* 48 *)

Inductive binary_word : nat -> Set :=
  empty_bin : binary_word 0
| cons_bin : forall m : nat, bool -> binary_word m -> binary_word (S m).

Fixpoint binary_word_concat (n m : nat) (w : binary_word n) (w' : binary_word m) {struct w}
  : binary_word (n + m) :=
  match w in binary_word p return binary_word (p + m) with
    empty_bin => w'
  | cons_bin q b w'' => cons_bin (q + m) b (binary_word_concat q m w'' w')
  end.

(* 49  and 50 skipping for now*)

(* 51 *)

Lemma l1 : forall x y : Empty_set, x = y.
Proof.
  intros x y.
  induction x.
Qed.

Lemma l2 : forall x y : Empty_set, ~ x=y.
Proof.
  intros x y.
  induction x.
Qed.
