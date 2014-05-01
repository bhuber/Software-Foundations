Require Export Basics.

(** For it to work, you need to use [coqc] to compile [Basics.v]
    into [Basics.vo].  (This is like making a .class file from a .java
    file, or a .o file from a .c file.)
  
    Here are two ways to compile your code:
  
     - CoqIDE:
   
         Open [Basics.v].
         In the "Compile" menu, click on "Compile Buffer".
   
     - Command line:
   
         Run [coqc Basics.v]

    *)

(* ###################################################################### *)
(** * Naming Cases *)

(** The fact that there is no explicit command for moving from
    one branch of a case analysis to the next can make proof scripts
    rather hard to read.  In larger proofs, with nested case analyses,
    it can even become hard to stay oriented when you're sitting with
    Coq and stepping through the proof.  (Imagine trying to remember
    that the first five subgoals belong to the inner case analysis and
    the remaining seven cases are what remains of the outer one...)
    Disciplined use of indentation and comments can help, but a better
    way is to use the [Case] tactic. *)

(* [Case] is not built into Coq: we need to define it ourselves.
    There is no need to understand how it works -- you can just skip
    over the definition to the example that follows.  It uses some
    facilities of Coq that we have not discussed -- the string
    library (just for the concrete syntax of quoted strings) and the
    [Ltac] command, which allows us to declare custom tactics.  Kudos
    to Aaron Bohannon for this nice hack! *)

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.
(** Here's an example of how [Case] is used.  Step through the
   following proof and observe how the context changes. *)


Theorem andb_true_elim1 : forall b c : bool,
    andb b c = true -> b = true.
Proof.
    intros b c H.
    destruct b.
    Case "b = true".
        reflexivity.
    Case "b = false".
        rewrite <- H.
        reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
    andb b c = true -> c = true.
Proof.
    intros b c H.
    destruct c.
    Case "c = true".
        reflexivity.
    Case "c = false".
        rewrite <- H.
        destruct b.
        simpl. reflexivity.
        simpl. reflexivity.
Qed.

Theorem plus_0_r : forall n:nat,
    n + 0 = n.
Proof.
    intros n. induction n as [| n'].
    Case "n = 0". reflexivity.
    Case "n = S n'".
        simpl.
        rewrite -> IHn'.
        reflexivity.
Qed.

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity. Qed.

(* Exercise - Basic Induction *)

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
    intros n. induction n as [| n'].
    Case "n = 0".
        simpl. reflexivity.
    Case "n = S n".
        simpl.
        rewrite -> IHn'.
        reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat, 
  S (n + m) = n + (S m).
Proof.
    intros n m. induction n as [| n'].
    Case "n = 0".
        simpl. reflexivity.
    Case "n = S n'".
        simpl.
        rewrite -> IHn'.
        reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
    intros n m. induction n as [| n'].
    Case "n = 0".
        rewrite -> plus_O_n.
        rewrite -> plus_0_r.
        reflexivity.
    Case "n = S n".
        simpl.
        rewrite -> IHn'.
        rewrite -> plus_n_Sm.
        reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
    intros n m p. induction n as [| n'].
    Case "n = 0".
        simpl. reflexivity.
    case "n = S n'".
        simpl.
        rewrite -> IHn'.
        reflexivity.
Qed.

(* Exercise - double plus *)
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
    intros n. induction n as [| n'].
    Case "n = 0".
        reflexivity.
    Case "n = S n'".
        simpl.
        rewrite -> IHn'.
        rewrite -> plus_n_Sm.
        reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n).
    Case "Proof of assertion". reflexivity.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
    Case "Proof of assertion".
    rewrite -> plus_comm. reflexivity.
  rewrite -> H. reflexivity. Qed.

(* Exercise - mult_comm *)

Theorem plus_swap : forall n m p : nat,
    n + (m + p) = m + (n + p).
Proof.
    intros n m p.
    rewrite -> plus_assoc.
    assert (H: n + m = m + n).
        Case "Proof by assertion".
        rewrite -> plus_comm. reflexivity.
    rewrite -> H.
    rewrite <- plus_assoc.
    reflexivity.
Qed.

Theorem mult_dist : forall n m p : nat,
    n * (m + p) = n * m + n * p.
Proof.
    intros n m p. induction n as [| n'].
    Case "n = 0".
        rewrite -> mult_0_1.
        reflexivity.
    Case "n = S n'".
        simpl.
        rewrite -> IHn'.
        assert (H: p + (n' * m + n' * p) = n' * m + (p + n' * p)).
            SCase "Proving Assertion".
            rewrite -> plus_swap.
            reflexivity.
        rewrite <- plus_assoc.
        rewrite -> H.
        rewrite -> plus_assoc.
        reflexivity.
Qed.

Theorem mult_1_r: forall n : nat,
    n * 1 = n.
Proof.
    intros n. induction n as [| n'].
    Case "n = 0".
        simpl. reflexivity.
    Case "n = S n'".
        simpl.
        rewrite -> IHn'.
        reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
    m * n = n * m.
Proof.
    intros m n. induction m as [| m'].
    Case "m = 0".
        rewrite -> mult_0_1.
        rewrite -> mult_0_r.
        reflexivity.
    Case "m = S m'".
        simpl.
        rewrite -> IHm'.
        assert (H: n * S m' = n * (1 + m')).
            SCase "Proof by assertion".
            simpl.
            reflexivity.
        rewrite -> H.
        rewrite -> mult_dist.
        rewrite -> mult_1_r.
        reflexivity.
Qed.

(* Exercise - evenb_n__oddb_Sn *)
Theorem evenb_n__oddb_Sn : forall n : nat,
    evenb n = negb (evenb (S n)).
Proof.
    intros n. induction n as [| n'].
    Case "n = 0".
        simpl.
        reflexivity.
    Case "n = S n'".
        simpl.
        rewrite -> IHn'.
        destruct n'.
        reflexivity.
        simpl.
        rewrite -> negb_involutive.
        reflexivity.
Qed.






