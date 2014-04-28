Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end. 

Eval compute in (next_weekday friday).

Eval compute in (next_weekday (next_weekday tuesday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.

Example test_next_weekday2:
  (next_weekday friday) = monday.

Proof. simpl. reflexivity. Qed.


Inductive bool : Type :=
  | true : bool | false : bool.

Definition negb (b:bool) :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (lhs:bool) (rhs:bool) :=
  match lhs with
  | true => rhs
  | false => false
  end.

Definition orb (lhs:bool) (rhs:bool) :=
  match lhs with
  | false => rhs
  | true => true
  end.

Example test_orb1: (orb true true) = true.
Proof. reflexivity. Qed.
Example test_orb2: (orb true false) = true.
Proof. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. reflexivity. Qed.
Example test_orb4: (orb false false) = false.
Proof. reflexivity. Qed.


Definition nandb (lhs:bool) (rhs:bool) :=
  match lhs with
  | false => true
  | true => (negb rhs)
  end.

Example test_nand1: (nandb true true) = false.
Proof. reflexivity. Qed.
Example test_nand2: (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nand3: (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nand4: (nandb false false) = true.
Proof. reflexivity. Qed.

Check true.

Check (negb true).


Module Playground1.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Definition pred (n:nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

End Playground1.

Definition minustwo (n:nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Check (S (S (S (S O)))).

Eval simpl in (minustwo 4).

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1: (oddb (S O)) = true.
Proof. reflexivity. Qed.
Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof. reflexivity. Qed.

Module Playground2.

Fixpoint plus (a:nat) (b:nat) : nat :=
  match a with
  | O => b
  | S a' => (plus a' (S b))
  end.

Eval simpl in (plus (S (S (S O))) (S (S O))).

Fixpoint mult (a b: nat) :=
  match a with
  | O => O
  | S a' => plus b (mult a' b)
  end.

End Playground2.

Example test_mult_0_1: (mult 0 0) = 0.
Proof. reflexivity. Qed.
Example test_mult_0_2: (mult 0 3) = 0.
Proof. reflexivity. Qed.
Example test_mult_0_3: (mult 3 0) = 0.
Proof. reflexivity. Qed.

Example test_mult_1_1: (mult 1 0) = 0.
Proof. reflexivity. Qed.
Example test_mult_1_2: (mult 1 1) = 1.
Proof. reflexivity. Qed.
Example test_mult_1_3: (mult 1 3) = 3.
Proof. reflexivity. Qed.
Example test_mult_1_4: (mult 4 1) = 4.
Proof. reflexivity. Qed.

Fixpoint minus (a b:nat) :=
  match a, b with
  | O, _ => O
  | S _, O => a
  | S a', S b' => minus a' b'
  end.

Fixpoint exp (base power : nat) :=
  match power with
  | O => S O
  | S power' => mult base (exp base power')
  end.

Example test_exp1: (exp 0 0) = 1.
Proof. reflexivity. Qed.
Example test_exp2: (exp 1 5) = 1.
Proof. reflexivity. Qed.
Example test_exp3: (exp 2 6) = 64.
Proof. reflexivity. Qed.
Example test_exp4: (exp 5 1) = 5.
Proof. reflexivity. Qed.
Example test_exp5: (exp 5 0) = 1.
Proof. reflexivity. Qed.

(* Exercise 1 *)

Fixpoint factorial (n:nat) :=
  match n with
  | O => S O
  | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.

Notation "x + y" :=
  (plus x y)
    (at level 50, left associativity)
    : nat_scope.

Notation "x - y" :=
  (minus x y)
    (at level 50, left associativity)
    : nat_scope.

Notation "x * y" :=
  (mult x y)
    (at level 40, left associativity)
    : nat_scope.

Check (((0 + 1) * 2) - 3).

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. reflexivity. Qed.

Definition blt_nat (a b : nat) : bool :=
  (andb (ble_nat a b) (negb (beq_nat a b))).

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. reflexivity. Qed.

(* Proof by Simplification *)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_1_1 : forall n: nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_0_1 : forall n: nat, 0 * n = 0.
  intros n. reflexivity. Qed.

(*
Theorem plus_commute : forall a b: nat, a + b = b + a.
  intros a b. simpl. Qed.
*)

Theorem plus_id_example : forall n m : nat,
  n = m -> n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite <- H.
  reflexivity. Qed.

(* Exercise plus_id_exercise *)
Theorem plus_id_exercies : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1 H2.
  rewrite -> H1.
  rewrite <- H2.
  reflexivity.
  Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.
  Qed.

(* Exercise 2 - mult_S_1 *)
Theorem mult_S_1 : forall n m : nat,
  m = S n -> m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite -> plus_1_1.
  rewrite <- H.
  reflexivity.
  Qed.

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
    reflexivity.
    reflexivity.
    Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
    reflexivity.
    reflexivity.
    Qed.

(* Exercise 1 - zero_nbeq_plus_1 *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros n. destruct n as [| n'].
    reflexivity.
    reflexivity.
    Qed.

(* Exercise - Boolean functions *)
Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall x : bool, f x = x) ->
  forall b : bool, f (f b) = b.
Proof.
  intros f H b.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
  Qed.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall x : bool, f x = negb x) ->
  forall b : bool, f (f b) = b.
Proof.
  intros f H b.
  rewrite -> H.
  rewrite -> H.
  rewrite -> negb_involutive.
  reflexivity.
  Qed.
  