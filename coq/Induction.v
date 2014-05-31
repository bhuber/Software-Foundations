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

(* Exercise - optional more exercises *)

(*
Take a piece of paper. For each of the following
theorems, first think about whether (a) it can be
proved using only simplification and rewriting, (b) it
also requires case analysis (destruct), or (c) it also
requires induction. Write down your prediction. Then
    fill in the proof. (There is no need to turn in
    your piece of paper; this is just to encourage you
    to reflect before hacking!)
*)


Theorem ble_nat_refl : forall n:nat,
  true = ble_nat n n.
Proof.
    (* Guess: Induction required *)
    intros n. induction n as [| n'].
    Case "n = 0".
        simpl. reflexivity.
    Case "n = S n'".
        simpl.
        rewrite -> IHn'.
        reflexivity.
Qed.

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
    (* Guess: simpl. *)
    simpl. reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
    (* Guess: destruct *)
    intros b. destruct b.
    simpl. reflexivity.
    simpl. reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat, 
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
    (* Guess: induction *)
    intros n m p H. induction p as [| p'].
    Case "p = 0".
        simpl. rewrite -> H. reflexivity.
    Case "p = S p'".
        simpl.
        rewrite -> IHp'.
        reflexivity.
Qed.

Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
    (* Guess: simpl. *)
    simpl. reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
    (* Guess: simpl. *)
    simpl.
    intros n.
    rewrite plus_0_r.
    reflexivity.
    (* Was really rewrite, and induction indirectly *)
Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
    (* Guess: destruct *)
    intros b c. destruct b.
    simpl.
    destruct c.
    simpl. reflexivity.
    simpl. reflexivity.
    destruct c.
    simpl. reflexivity.
    simpl. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
    (* Guess: rewrite *)
    intros n m p.
    rewrite -> mult_comm.
    rewrite -> mult_dist.
    rewrite -> mult_comm.
    assert (H: p * m = m * p).
        Case "Proving assertion".
        rewrite -> mult_comm.
        reflexivity.
    rewrite -> H.
    reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
    (* Guess: Induction *)
    intros n m p. induction n as [| n'].
    Case "n = 0".
        simpl.
        reflexivity.
    Case "n = S n'".
        simpl.
        rewrite -> IHn'.
        rewrite -> mult_plus_distr_r.
        reflexivity.
Qed.

(** [] *)

(** **** Exercise: 2 stars, optional (beq_nat_refl) *)
(** Prove the following theorem.  Putting [true] on the left-hand side
of the equality may seem odd, but this is how the theorem is stated in
the standard library, so we follow suit.  Since rewriting 
works equally well in either direction, we will have no 
problem using the theorem no matter which way we state it. *)

Theorem beq_nat_refl : forall n : nat, 
  true = beq_nat n n.
Proof.
    intros n. induction n as [| n'].
    Case "n = 0".
        simpl. reflexivity.
    Case "n = S n'".
        simpl.
        rewrite -> IHn'.
        reflexivity.
Qed.

(** [] *)

(** **** Exercise: 2 stars, optional (plus_swap') *)
(** The [replace] tactic allows you to specify a particular subterm to
   rewrite and what you want it rewritten to.  More precisely,
   [replace (t) with (u)] replaces (all copies of) expression [t] in
   the goal by expression [u], and generates [t = u] as an additional
   subgoal. This is often useful when a plain [rewrite] acts on the wrong
   part of the goal.  

   Use the [replace] tactic to do a proof of [plus_swap'], just like
   [plus_swap] but without needing [assert (n + m = m + n)]. 
*)

Theorem plus_swap' : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
    intros n m p.
    rewrite -> plus_assoc.
    replace (n + m) with (m + n).
    rewrite <- plus_assoc. reflexivity.
    rewrite -> plus_comm. reflexivity.
Qed.
(** [] *)


(** **** Exercise: 3 stars (binary_commute) *)
(** Recall the [increment] and [binary-to-unary] functions that you
    wrote for the [binary] exercise in the [Basics] chapter.  Prove
    that these functions commute -- that is, incrementing a binary
    number and then converting it to unary yields the same result as
    first converting it to unary and then incrementing.

    (Before you start working on this exercise, please copy the
    definitions from your solution to the [binary] exercise here so
    that this file can be graded on its own.  If you find yourself
    wanting to change your original definitions to make the property
    easier to prove, feel free to do so.) *)

(* FILL IN HERE *)

Fixpoint incb (b:bin) : bin :=
    match b with
    | BO => BS BO
    | BS BO => D (BS BO)
    | BS (BS BO) => BS (D (BS BO))
    | BS (BS n') => BS (D n')
    | D n' => BS (D n')
    | BS (D n') => D (incb n')
    end.

Fixpoint bin_to_nat (b:bin) : nat :=
    match b with
    | BO => O
    | BS n' => S (bin_to_nat n')
    | D n' => (plus (bin_to_nat n') (bin_to_nat n'))
    end.

Theorem binary_commute: forall b:bin,
    (bin_to_nat (incb b)) = (S (bin_to_nat b)).
Proof.
    intros b. induction b as [b0 | be | bo].
    Case "b = 0".
        simpl.
        reflexivity.
    Case "b is even".
        simpl.
        reflexivity.
    Case "b is odd".
        induction incb as [bn1 | bn2 | bn3].
        simpl. reflexivity.
        simpl. rewrite <- IHbo0.
        destruct bo.

        assert (H1: bin_to_nat (BS bo) = S (bin_to_nat bo)).
        SCase "Proving Assertion H1".
            simpl. reflexivity.
        rewrite -> H1.
        simpl.
        (* assert (H2: bin_to_nat (incb (BS bo)) = bin_to_nat (BS (BS bo))). *)
        assert (H2: incb (BS bo) = BS (BS bo)).
            simpl.
            destruct bo.
            simpl.
            replace (D (BS BO) = BS (BS BO)) with (incb (D (BS BO)) = incb (D (BS BO))).
            simpl. reflexivity.
        SCase "Proving Assertion H2".
            simpl.
            destruct bo as [| boe | boo].
            simpl.
            assert (Ht: incb (D (BS BO)) = incb (BS (BS BO))).
                simpl. reflexivity.

        simpl.
        induction bo.
        simpl. reflexivity.
        simpl. rewrite -> IHbo0.
        rewrite -> H1.
        rewrite <- IHbo.

        rewrite -> H2.
        destruct bo.
Qed.




(** [] *)


(** **** Exercise: 5 stars, advanced (binary_inverse) *)
(** This exercise is a continuation of the previous exercise about
    binary numbers.  You will need your definitions and theorems from
    the previous exercise to complete this one.

    (a) First, write a function to convert natural numbers to binary
        numbers.  Then prove that starting with any natural number,
        converting to binary, then converting back yields the same
        natural number you started with.

    (b) You might naturally think that we should also prove the
        opposite direction: that starting with a binary number,
        converting to a natural, and then back to binary yields the
        same number we started with.  However, it is not true!
        Explain what the problem is.

    (c) Define a function [normalize] from binary numbers to binary
        numbers such that for any binary number b, converting to a
        natural and then back to binary yields [(normalize b)].  Prove
        it.

    Again, feel free to change your earlier definitions if this helps
    here. 
*)

(* FILL IN HERE *)
(** [] *)

(* ###################################################################### *)
(** * Advanced Material *)

(** ** Formal vs. Informal Proof *)

(** "Informal proofs are algorithms; formal proofs are code." *)

(** The question of what, exactly, constitutes a "proof" of a
    mathematical claim has challenged philosophers for millenia.  A
    rough and ready definition, though, could be this: a proof of a
    mathematical proposition [P] is a written (or spoken) text that
    instills in the reader or hearer the certainty that [P] is true.
    That is, a proof is an act of communication.

    Now, acts of communication may involve different sorts of readers.
    On one hand, the "reader" can be a program like Coq, in which case
    the "belief" that is instilled is a simple mechanical check that
    [P] can be derived from a certain set of formal logical rules, and
    the proof is a recipe that guides the program in performing this
    check.  Such recipes are _formal_ proofs.

    Alternatively, the reader can be a human being, in which case the
    proof will be written in English or some other natural language,
    thus necessarily _informal_.  Here, the criteria for success are
    less clearly specified.  A "good" proof is one that makes the
    reader believe [P].  But the same proof may be read by many
    different readers, some of whom may be convinced by a particular
    way of phrasing the argument, while others may not be.  One reader
    may be particularly pedantic, inexperienced, or just plain
    thick-headed; the only way to convince them will be to make the
    argument in painstaking detail.  But another reader, more familiar
    in the area, may find all this detail so overwhelming that they
    lose the overall thread.  All they want is to be told the main
    ideas, because it is easier to fill in the details for themselves.
    Ultimately, there is no universal standard, because there is no
    single way of writing an informal proof that is guaranteed to
    convince every conceivable reader.  In practice, however,
    mathematicians have developed a rich set of conventions and idioms
    for writing about complex mathematical objects that, within a
    certain community, make communication fairly reliable.  The
    conventions of this stylized form of communication give a fairly
    clear standard for judging proofs good or bad.

    Because we are using Coq in this course, we will be working
    heavily with formal proofs.  But this doesn't mean we can ignore
    the informal ones!  Formal proofs are useful in many ways, but
    they are _not_ very efficient ways of communicating ideas between
    human beings. *)

(** For example, here is a proof that addition is associative: *)

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n']. reflexivity. 
  simpl. rewrite -> IHn'. reflexivity.  Qed.

(** Coq is perfectly happy with this as a proof.  For a human,
    however, it is difficult to make much sense of it.  If you're used
    to Coq you can probably step through the tactics one after the
    other in your mind and imagine the state of the context and goal
    stack at each point, but if the proof were even a little bit more
    complicated this would be next to impossible.  Instead, a
    mathematician might write it something like this: *)
(** - _Theorem_: For any [n], [m] and [p],
      n + (m + p) = (n + m) + p.
    _Proof_: By induction on [n].

    - First, suppose [n = 0].  We must show 
        0 + (m + p) = (0 + m) + p.  
      This follows directly from the definition of [+].

    - Next, suppose [n = S n'], where
        n' + (m + p) = (n' + m) + p.
      We must show
        (S n') + (m + p) = ((S n') + m) + p.
      By the definition of [+], this follows from
        S (n' + (m + p)) = S ((n' + m) + p),
      which is immediate from the induction hypothesis. [] *)

(** The overall form of the proof is basically similar.  This is
    no accident: Coq has been designed so that its [induction] tactic
    generates the same sub-goals, in the same order, as the bullet
    points that a mathematician would write.  But there are
    significant differences of detail: the formal proof is much more
    explicit in some ways (e.g., the use of [reflexivity]) but much
    less explicit in others (in particular, the "proof state" at any
    given point in the Coq proof is completely implicit, whereas the
    informal proof reminds the reader several times where things
    stand). *)

(** Here is a formal proof that shows the structure more
    clearly: *)

Theorem plus_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n']. 
  Case "n = 0".
    reflexivity. 
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.   Qed.

(** **** Exercise: 2 stars, advanced (plus_comm_informal) *)
(** Translate your solution for [plus_comm] into an informal proof. *)

(** Theorem: Addition is commutative.
 
    Proof: (* FILL IN HERE *)
[]
*)

(** **** Exercise: 2 stars, optional (beq_nat_refl_informal) *)
(** Write an informal proof of the following theorem, using the
    informal proof of [plus_assoc] as a model.  Don't just
    paraphrase the Coq tactics into English!
 
    Theorem: [true = beq_nat n n] for any [n].
    
    Proof: (* FILL IN HERE *)
[]
 *)

(* $Date: 2013-07-17 16:19:11 -0400 (Wed, 17 Jul 2013) $ *)





