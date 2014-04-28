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

End Playground2.