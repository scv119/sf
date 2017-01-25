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

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.


Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b:bool) :bool :=
  match b with
    | true => false
    | false => true
  end.

Definition andb (b1: bool) (b2:bool) : bool :=
  match b1 with
    | true => b2
    | false => false
  end.

Definition orb (b1: bool) (b2:bool) : bool :=
  match b1 with
    | true => true
    | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Example test_orb3: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb4: (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Infix "&&" := andb.
Infix "||" := orb.

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition nandb (b1: bool) (b2:bool) : bool :=
  match b1, b2 with
    | true, true => false
    | _, _ => true
  end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1: bool) (b2:bool) (b3:bool) : bool :=
  match b1, b2, b3 with
    | true, true, true => true
    | _, _, _ => false
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Module Playground1.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with 
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Check (S (S (S (S O)))).

Compute (minustwo 4).

Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n:nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.

Example test_oddb2: oddb 4 =  false.
Proof. reflexivity. Qed.

Module Playground2.

Fixpoint plus (n: nat) (m: nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Compute (plus 3 2).

Fixpoint mult (n m : nat) : nat :=
  match n with 
    | O => O
    | S n' => plus m (mult n' m)
  end.

Example test_multi: (mult 3 3) = 9.
Proof. reflexivity. Qed.

Fixpoint minus (n m : nat) : nat := 
  match n, m with
    | O, _ => O
    | S _, O => n
    | S n', S m' => minus n' m'
  end.
End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S n => mult base (exp base n)
  end.

(* Exc factorial *)
Fixpoint factorial (n:nat) : nat :=
  match n with
    | O => S O
    | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
  (at level 50, left associativity)
  : nat_scope.

Notation "x - y" := (minus x y)
  (at level 50, left associativity)
  : nat_scope.

Notation "x * y" := (mult x y)
  (at level 40, left associativity)
  : nat_scope.

Check ((0 + 1) + 1).
Example test_notation: ((0 + 1) + 1) = 2.
Proof. simpl. reflexivity. Qed.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
   | O => match m with
            | O => true
            | _ => false
          end
   | S n' => match m with
              | O => false
              | S m' => beq_nat n' m'
             end
  end.

Fixpoint leb (n m: nat): bool := 
  match n with
    | O => true
    | S n' =>
      match m with
        | O => false
        | S m' => leb n' m'
      end
  end.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

(* Exc blt_nat *)
Definition blt_nat (n m: nat) : bool :=
  match (beq_nat n m) with
    | true => false
    | false => leb n m
  end.

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

(* Proof by Simplification *)

Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem plus_1_n : forall n : nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_0_1 : forall n : nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_n_0 : forall n, n = n + 0.
Proof.
  intros n. simpl.

Abort.

(* This failed because `plus` can't handle undeterministic n as first argument *)

(* Proof by rewriting *)

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof.
  (* move both quantifiers into the context : *)
  intros n m.
  (* move the hypothesis into the context : *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite -> H.
  reflexivity. Qed.

(* Exc plus id *)
Theorem plus_id_excercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H.
  intros H'.
  rewrite -> H.
  rewrite -> H'.
  reflexivity. Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_0_n.
  reflexivity. Qed.

(* Exc mult S 1 *)
Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  rewrite <- plus_1_n.
  reflexivity. Qed.

(* Proof by Case Analysis *)
Theorem plus_1_neg_0_firsttry : forall n: nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  simpl.
Abort.

Theorem plus_1_neg_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
  - reflexivity.
  - reflexivity. Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity. Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
  Qed.

(* Exc andb_true_elem2 *)
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct c.
  - reflexivity.
  - rewrite <-H.
    destruct b.
    + reflexivity.
    + reflexivity.
  Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros [|n'].
  - reflexivity.
  - simpl. reflexivity.
  Qed.

Theorem identity_fn_applies_twice :
  forall (f: bool -> bool),
  (forall(x : bool), f x = x) ->
  forall (b: bool), f (f b) = b.
Proof.
  intros f H.
  intros x.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
  Qed.

Lemma true_andb : forall b :bool,
  andb true b = b.
Proof.
  intros b. reflexivity. Qed.

Lemma true_orb : forall b :bool,
  orb true b = true.
Proof.
  intros b. reflexivity. Qed.

Lemma false_andb : forall c :bool,
  andb false c = false.
Proof.
  intros b. reflexivity. Qed.

Lemma false_orb : forall c :bool,
  orb false c = c.
Proof.
  intros b. reflexivity. Qed.

Theorem andb_eq_orb :
  forall (b c: bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c H.
  destruct b.
  - rewrite <- true_andb. 
    rewrite -> H.
    rewrite -> true_orb.
    reflexivity.
  - rewrite <- false_orb.
    rewrite <- H.
    rewrite -> false_andb.
    reflexivity.
  Qed.


Inductive bin : Type :=
  | Zero : bin
  | Twice : bin -> bin
  | TwiceAndOne : bin -> bin.

Fixpoint incr (b : bin) : bin :=
  match b with
    | Zero => TwiceAndOne Zero
    | Twice b' => TwiceAndOne b'
    | TwiceAndOne b' => Twice (incr b')
  end.

Fixpoint bin_to_nat (b : bin) : nat :=
  match b with
    | Zero => 0
    | TwiceAndOne b' => 1 + 2 * (bin_to_nat b')
    | Twice b' => 2 * (bin_to_nat b')
  end.
